-- Prove2me | Theorems.Thm_HierADA_proposition_3_2
-- name    : HierADA.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:09:09.611244+00:00
-- url     : https://prove2.me/theorems/18222d2b-7d8a-4f53-ac26-4efb76fc3c10
-- title:
--   Proposition 3.2 — reference accuracy under bounded privacy (corrected: Lemma 3.1's explicit sample size)
-- statement:
--   Let $\alpha,\xi\in(0,\frac1{10})$ and let $p,\tau,\varepsilon_j,B_j$ be the parameters of Section 3.2. Run the auxiliary mechanism on independent blocks $S_1,\dots,S_p$ of i.i.d. samples from $P$, with any analyst, any Laplace noise scale $b>0$, and any block sizes $n_j$ and $\delta$ satisfying the assumptions of Lemma 3.1 with accuracy $\tau/64$ and failure probability $\xi/(p+1)$:
--
--   $$
--   n_j\ge\frac{1024}{(\tau/64)^2}\ln\frac{4(k+1)(p+1)}{\xi}\quad\text{for every }j,\qquad 0<\delta\le\frac{(\tau/64)(\xi/(p+1))}{32}.
--   $$
--
--   Suppose that
--
--   1. for every block $j$, the augmented transcript is $(\varepsilon_j,\delta)$-private with respect to $S_j$, the other blocks and the noise being part of the mechanism's randomness;
--   2. the probability that some noise draw of the execution has magnitude greater than $\tau/64$ is at most $\xi/(p+1)$.
--
--   Then, with probability at least $1-\xi$, the conclusions (1)–(3) of the good event $E$ hold simultaneously. Moreover
--
--   $$
--   \sum_{j=1}^{p-1}4^{j-1}\varepsilon_j^2=\frac{p-1}{p}\le1,
--   $$
--
--   so reference vectors with $R_j(u_j)\le\varepsilon_j^2$ satisfy $\sum_{j=1}^{p-1}4^{j-1}R_j(u_j)\le\frac{p-1}{p}$ (Equation (7)).
--
--   The proposition turns privacy into the existence of accurate near-uniform reference weights in every block at once, and bounds the initial value of the potential used in Proposition 3.4.
--
--   **Formalization Note** Privacy is the published `ContinualCounting.IsApproxDP` for the neighbour relation `PrivLearn.Generic.Neighbors`. The augmented transcript is assumed measurable in the noise, so that its law is a genuine push-forward; Theorem 3.7 proves this for the auxiliary execution.
--
--   Differences from the source:
--   - reading: “Let α, δ < 1/10 be the accuracy and failure parameters” (p.18) → 0 < α < 1/10 and 0 < ξ < 1/10; reason: δ there is the failure parameter, called ξ in the rest of Section 3; δ is later the privacy slack τξ/(4096(p+1))
--   - correction: “nj and δ satisfy the assumptions of Lemma 3.1 with accuracy τ/64 and failure probability ξ/(p + 1)”, whose sample size is printed as r = O((1/α²) log(k/ξ)) → n_j ≥ (1024/(τ/64)²) ln(4(k+1)(p+1)/ξ) for every j and 0 < δ ≤ (τ/64)(ξ/(p+1))/32; reason: the assumptions of the corrected Lemma 3.1 at accuracy τ/64 and failure ξ/(p+1) (its O-form is false, see Lemma 3.1); this is the form checked on p.25; the other assumptions of Lemma 3.1 (ε_j ∈ [0, 1], δ < 1) follow
--   - reading: “the transcript T is (εj, δ)-private with respect to block Sj” → IsApproxDP of s ↦ augLawAvg … j s: the other blocks i.i.d. from P and the noise from its law; reason: the proof regards “the other independent blocks as part of the mechanism's randomness” (p.19); this is the weaker of the two readings, so the hypothesis is the weaker one
--   - encoding: the law of the transcript (implicit) → hypothesis that the augmented transcript is a measurable function of the noise; reason: Measure.map of a non-measurable map is 0 in Lean, which would make the privacy hypothesis vacuous; the transcript is measurable (Theorem 3.7)
--   - encoding: the noise scale b, not yet fixed in Section 3.2 → any b > 0, the noise law of noiseLaw with scale b; reason: the proposition is stated before b is chosen (p.24)
--   - encoding: with probability at least 1 − ξ, (1)–(3) hold → the complement of the good event has probability at most ξ; reason: complementary events
--   - encoding: blocks and edges numbered from 1, multipliers 4^{j−1} → 0-based Fin p indices, multipliers 4^j; reason: renumbering only
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Proposition 3.2, p.18 (continued on p.19), Equation (7)

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_params__e3298e
import Definitions.Def_HierADA_auxRun
import Definitions.Def_ContinualCounting_IsApproxDP
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_HierADA_augLawAvg
import Definitions.Def_HierADA_jointProb
import Definitions.Def_HierADA_goodEvent
import Definitions.Def_HierADA_penalty

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Proposition 3.2 (Reference accuracy under bounded privacy)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–
Yu–Zhou, *Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint
(version of 2026-11-03, sha256 f220ae51…), Proposition 3.2, pp.18–19, Equation (7).

Let `α, ξ ∈ (0, 1/10)`, take `p, τ, ε_j, B_j` as in Section 3.2 (`params α ξ k`), and let the
auxiliary mechanism use any noise scale `b > 0`, any block sizes `n_j` and any `δ` such that, for
every block `j`, `n_j ≥ (1024/(τ/64)²) ln(4(k+1)(p+1)/ξ)` and `0 < δ ≤ (τ/64)(ξ/(p+1))/32` (the
assumptions of Lemma 3.1 with accuracy `τ/64` and failure probability `ξ/(p+1)`). Suppose that for
every block `j` the augmented transcript is `(ε_j, δ)`-private with respect to block `S_j` (the other
blocks and the noise being the mechanism's randomness), and that the probability that some noise draw
of the execution has magnitude greater than `τ/64` is at most `ξ/(p+1)`. Then with probability at
least `1 − ξ` the conclusions (1)–(3) of the good event `E` hold. Moreover
`∑_{j=1}^{p-1} 4^{j-1} ε_j² = (p − 1)/p ≤ 1`, so reference vectors with `R_j(u_j) ≤ ε_j²` satisfy
`P := ∑_{j=1}^{p-1} 4^{j-1} R_j(u_j) ≤ (p − 1)/p` (Equation (7)).

**Formalization Note.** Indices are 0-based (the paper's `4^{j-1}` is `4^j`). `α, δ < 1/10` on p.18
is read as `α, ξ < 1/10` (the failure parameter is called `ξ` in Section 3; `δ` is the privacy
slack). The privacy hypothesis is in the averaged form of the proof ("we regard the other independent
blocks as part of the mechanism's randomness", p.19): `augLawAvg`. The augmented transcript is assumed
measurable in the noise, so that its law is the push-forward (this holds for the auxiliary execution
and is a conclusion of Theorem 3.7). The noise law is `noiseLaw` with scale `b`. -/
theorem proposition_3_2 {X : Type} [Fintype X] (α ξ : ℝ) (hα0 : 0 < α) (hα : α < 1 / 10)
    (hξ0 : 0 < ξ) (hξ : ξ < 1 / 10) (k : ℕ) (P : PMF X) (A : Analyst X) (δ b : ℝ) (hb : 0 < b)
    (n : Fin (params α ξ k).p → ℕ)
    (hn : ∀ j, 1024 / ((params α ξ k).τ / 64) ^ 2 *
        Real.log (4 * ((k : ℝ) + 1) * ((params α ξ k).p + 1) / ξ) ≤ n j)
    (hδ0 : 0 < δ) (hδ : δ ≤ (params α ξ k).τ / 64 * (ξ / ((params α ξ k).p + 1)) / 32)
    (hmeas : ∀ S : (j : Fin (params α ξ k).p) → Fin (n j) → X,
      Measurable fun z => (auxRun { params α ξ k with b := b } n S z A k).aug)
    (hpriv : ∀ j, ContinualCounting.IsApproxDP PrivLearn.Generic.Neighbors (augLawAvg { params α ξ k with b := b } k P n A j)
      ((params α ξ k).ε j) δ)
    (hnoise : jointProb { params α ξ k with b := b } k P n
        {ω | ∃ v ∈ (auxRun { params α ξ k with b := b } n ω.1 ω.2 A k).noiseUsed,
          (params α ξ k).τ / 64 < |v|} ≤
      ENNReal.ofReal (ξ / ((params α ξ k).p + 1))) :
    jointProb { params α ξ k with b := b } k P n
        (goodEvent { params α ξ k with b := b } k P n A)ᶜ ≤ ENNReal.ofReal ξ ∧
    (∑ j : Fin (params α ξ k).p, if j.val + 1 < (params α ξ k).p then
        (4 : ℝ) ^ j.val * (params α ξ k).ε j ^ 2 else 0) =
      ((params α ξ k).p - 1 : ℝ) / (params α ξ k).p ∧
    ((params α ξ k).p - 1 : ℝ) / (params α ξ k).p ≤ 1 ∧
    ∀ u : (j : Fin (params α ξ k).p) → Fin (n j) → ℝ,
      (∀ j : Fin (params α ξ k).p, j.val + 1 < (params α ξ k).p →
        penalty (n j) (u j) ≤ (params α ξ k).ε j ^ 2) →
      (∑ j : Fin (params α ξ k).p, if j.val + 1 < (params α ξ k).p then
          (4 : ℝ) ^ j.val * penalty (n j) (u j) else 0) ≤
        ((params α ξ k).p - 1 : ℝ) / (params α ξ k).p := by sorry

end HierADA
