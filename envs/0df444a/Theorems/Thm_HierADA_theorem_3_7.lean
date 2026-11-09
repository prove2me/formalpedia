-- Prove2me | Theorems.Thm_HierADA_theorem_3_7
-- name    : HierADA.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:07:25.075858+00:00
-- url     : https://prove2.me/theorems/ce55e18d-9b12-4869-afee-a8b19d2b930f
-- title:
--   Theorem 3.7 — privacy and the hypotheses for progress
-- statement:
--   Let $\alpha,\xi\in(0,\frac1{10})$ and take all parameters of Sections 3.2–3.3: $p,\tau,\varepsilon_j,B_j$, the component counts $C_j$ of Equation (15), $\delta=\frac{\tau\xi}{4096(p+1)}$, $L$ and $b=\frac\tau{256L}$. Let the block sizes satisfy
--
--   $$
--   n_j\ge\Big\lceil\max\Big(\frac{128\sqrt{C_jL}}{b\,\varepsilon_j},\ \frac{2^{22}L}{\tau^2}\Big)\Big\rceil\quad\text{for every block }j .
--   $$
--
--   Then, for every distribution $P$ and every analyst:
--
--   1. the augmented transcript of the auxiliary execution is a measurable function of the noise;
--   2. for every block $j$ and every fixed value of the other blocks, the augmented transcript is $(\varepsilon_j,\delta)$-private with respect to replacing one sample in $S_j$;
--   3. the hypotheses of Proposition 3.2 hold:
--      - $n_j\ge\frac{1024}{(\tau/64)^2}\ln\frac{4(k+1)(p+1)}{\xi}$;
--      - $0<\delta\le\frac{(\tau/64)(\xi/(p+1))}{32}$;
--      - privacy with respect to $S_j$ when the other blocks are random;
--      - the probability that some noise draw exceeds $\tau/64$ in magnitude is at most $\frac\xi{p+1}$;
--   4. consequently $\Pr[E]\ge1-\xi$.
--
--   The theorem is the privacy half of the argument. It holds for every execution, including those that reach a correction limit, and does not use the progress bound.
--
--   **Formalization Note** Privacy is the published `ContinualCounting.IsApproxDP` for the neighbour relation `PrivLearn.Generic.Neighbors`. Clause 1 makes the transcript laws in clauses 2–3 genuine push-forwards.
--
--   Differences from the source:
--   - reading: “Let α, δ < 1/10 be the accuracy and failure parameters” (p.18) → 0 < α < 1/10 and 0 < ξ < 1/10; reason: δ there is the failure parameter, called ξ in the rest of Section 3; δ is later the privacy slack τξ/(4096(p+1))
--   - reading: Algorithm 2 scans while j ≤ p and updates G_{j+1} if j + 1 ≤ p → only the edges j ∈ [1, p) are scanned and the anchor's score is never updated; reason: there is no block p + 1, the anchor's weights stay uniform (p.13), and the proof of Proposition 3.4 says that on the last edge only block p − 1 is updated (p.22)
--   - reading: “(εj, δ)-private with respect to replacing one sample in Sj” → for every fixed value of the other blocks (augLaw), and also with the other blocks random (augLawAvg) as a hypothesis of Proposition 3.2; reason: the proof fixes the other sample blocks (p.25); this is the stronger reading and implies the averaged one
--   - generalization: block sizes n_1 = O((√k/α + 1/α²) log⁴(2k/(αξ))), n_j = O((1/α²) log⁴(2k/(αξ))) “with sufficiently large constants so that nj ≥ ⌈max(…)⌉” → every n_j ≥ ⌈max(128√(C_j L)/(b ε_j), 2²² L/τ²)⌉; reason: the proof uses only the lower bound; the paper's choice satisfies it
--   - encoding: the law of the augmented transcript (implicit) → an added clause: the augmented transcript is a measurable function of the noise; reason: Measure.map of a non-measurable map is 0 in Lean, which would make the privacy clauses vacuous
--   - encoding: Pr[E] ≥ 1 − ξ → the complement of the good event has probability at most ξ; reason: complementary events
--   - encoding: blocks and edges numbered from 1, multipliers 4^{j−1} → 0-based Fin p indices, multipliers 4^j; reason: renumbering only
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Theorem 3.7, p.24, with the parameter choices of p.24 (Equation (15), δ, L, b, n_j)

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_params__e3298e
import Definitions.Def_HierADA_auxRun
import Definitions.Def_ContinualCounting_IsApproxDP
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_HierADA_augLaw
import Definitions.Def_HierADA_augLawAvg
import Definitions.Def_HierADA_jointProb
import Definitions.Def_HierADA_goodEvent

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Theorem 3.7 (Privacy and the hypotheses for progress)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–
Zhou, *Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint
(version of 2026-11-03, sha256 f220ae51…), Theorem 3.7, p.24, with the parameter choices of the
paragraph before it (Equation (15), `δ`, `L`, `b`, `n_j`).

Let `α, ξ ∈ (0, 1/10)`, take all parameters as in Sections 3.2–3.3 (`params α ξ k`), and let the
block sizes satisfy `n_j ≥ ⌈max(128√(C_j L)/(b ε_j), 2²² L/τ²)⌉` for every block `j`. Then, for every
distribution `P` and analyst `A`:
1. the augmented transcript of the auxiliary execution is a measurable function of the noise;
2. for every block `j` and every fixed value of the other blocks, the augmented transcript is
   `(ε_j, δ)`-private with respect to replacing one sample in `S_j`;
3. the hypotheses of Proposition 3.2 hold: the sample-size bound
   `n_j ≥ (1024/(τ/64)²) ln(4(k+1)(p+1)/ξ)`, `0 < δ ≤ (τ/64)(ξ/(p+1))/32`, privacy with the other
   blocks random, and the probability that some noise draw exceeds `τ/64` in magnitude is at most
   `ξ/(p+1)`;
4. consequently `Pr[E] ≥ 1 − ξ`.

**Formalization Note.** Indices are 0-based. The privacy clause 2 is stated for every fixed value of
the other blocks, as in the proof ("Fix the other sample blocks", p.25); it implies the averaged form
of clause 3. Clause 1 makes the laws in clauses 2–3 genuine push-forwards (it is implicit in the
paper). `α, δ < 1/10` on p.18 is read as `α, ξ < 1/10`. -/
theorem theorem_3_7 {X : Type} [Fintype X] (α ξ : ℝ) (hα0 : 0 < α) (hα : α < 1 / 10)
    (hξ0 : 0 < ξ) (hξ : ξ < 1 / 10) (k : ℕ) (P : PMF X) (A : Analyst X)
    (n : Fin (params α ξ k).p → ℕ)
    (hn : ∀ j, ⌈max (128 * Real.sqrt ((params α ξ k).C j * (params α ξ k).L) /
          ((params α ξ k).b * (params α ξ k).ε j))
        (2 ^ 22 * (params α ξ k).L / (params α ξ k).τ ^ 2)⌉₊ ≤ n j) :
    (∀ S : (j : Fin (params α ξ k).p) → Fin (n j) → X,
      Measurable fun z => (auxRun (params α ξ k) n S z A k).aug) ∧
    (∀ (j : Fin (params α ξ k).p) (S : (j : Fin (params α ξ k).p) → Fin (n j) → X),
      ContinualCounting.IsApproxDP PrivLearn.Generic.Neighbors (augLaw (params α ξ k) k n A S j) ((params α ξ k).ε j) (params α ξ k).δ) ∧
    ((∀ j, 1024 / ((params α ξ k).τ / 64) ^ 2 *
        Real.log (4 * ((k : ℝ) + 1) * ((params α ξ k).p + 1) / ξ) ≤ n j) ∧
      0 < (params α ξ k).δ ∧
      (params α ξ k).δ ≤ (params α ξ k).τ / 64 * (ξ / ((params α ξ k).p + 1)) / 32 ∧
      (∀ j, ContinualCounting.IsApproxDP PrivLearn.Generic.Neighbors (augLawAvg (params α ξ k) k P n A j) ((params α ξ k).ε j)
        (params α ξ k).δ) ∧
      jointProb (params α ξ k) k P n
          {ω | ∃ v ∈ (auxRun (params α ξ k) n ω.1 ω.2 A k).noiseUsed,
            (params α ξ k).τ / 64 < |v|} ≤
        ENNReal.ofReal (ξ / ((params α ξ k).p + 1))) ∧
    jointProb (params α ξ k) k P n (goodEvent (params α ξ k) k P n A)ᶜ ≤ ENNReal.ofReal ξ := by sorry

end HierADA
