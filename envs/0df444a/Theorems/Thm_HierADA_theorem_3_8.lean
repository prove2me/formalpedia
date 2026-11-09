-- Prove2me | Theorems.Thm_HierADA_theorem_3_8
-- name    : HierADA.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:17.66783+00:00
-- url     : https://prove2.me/theorems/f573c88a-e7d4-4a03-819f-b22920dffbce
-- title:
--   Theorem 3.8 — $k$ adaptive queries to error $\alpha$ from $O((\sqrt k/\alpha+1/\alpha^2)\log^5\frac{k}{\alpha\xi})$ samples (corrected: $\alpha\in(0,1)$)
-- statement:
--   There is a universal constant $C$ such that for every accuracy $\alpha\in(0,1)$, every failure probability $\xi\in(0,1)$ and every number of queries $k$, there are a sample size
--
--   $$
--   N\le C\Big(\frac{\sqrt k}{\alpha}+\frac1{\alpha^2}\Big)\log^5\frac{k}{\alpha\xi}
--   $$
--
--   and a probability space of seeds with the following property. For every finite domain $U$ there is a randomized mechanism on $N$ samples such that, for every distribution $D$ on $U$ and every adaptive analyst submitting queries $f_t:U\to[0,1]$,
--
--   $$
--   \Pr_{S\sim D^N,\ \omega}\Big[\big|a_t-\mathbb E_{X\sim D}f_t(X)\big|\le\alpha\ \text{for all }t\le k\Big]\ge1-\xi .
--   $$
--
--   Moreover, the failure event is measurable in the seed.
--
--   This is the paper's main theorem. Up to logarithmic factors it matches the lower bound $\tilde\Omega(\sqrt k/\alpha+1/\alpha^2)$ of Hardt–Ullman and Steinke–Ullman for unrestricted domains, and improves the earlier $\tilde O(\sqrt k/\alpha^2)$.
--
--   **Formalization Note** Analysts are deterministic maps from the history to the next query. The interaction, the population mean and the error event are those of the published `IsRandomnessNecessaryADA.Plain`. The sample size and the seed space are chosen before the domain; the mechanism may depend on the domain but never on $D$.
--
--   Differences from the source:
--   - correction: “For any accuracy parameter α > 0” → 0 < α < 1; reason: for α > k/ξ the factor log⁵(k/(αξ)) is negative and no N ≥ 0 satisfies the bound for any C (k = 1, ξ = 1/2, α = 4); α ∈ (0, 1) is the range of Theorem 1.2
--   - reading: a randomized mechanism; “against any adaptive analyst” → a seed drawn once from a probability space, each answer a deterministic function of (seed, sample, history, current query); analysts deterministic maps from the history to the next query; reason: the proof pre-assigns all randomness (p.25); Definition 2.1 and Lemma 3.1 fix the analyst rule
--   - reading: with probability at least 1 − ξ (over the samples and the mechanism's coins) → failureProb ≤ ξ: the sum over samples of P^N(s) times the seed measure of the bad section (outer measure); reason: the product law on a finite sample space; with measurable sections it is the ordinary probability
--   - encoding: the probability of the failure event (implicit) → an added clause: every section of the failure event is measurable in the seed; reason: the paper presupposes the event has a probability; it holds for the paper's mechanism, whose answers lie on a finite grid
--   - encoding: O(·), log → one constant C quantified before α, ξ, k; natural logarithm; k ∈ ℕ including k = 0; reason: the standard meaning of O; another base changes only C; at k = 0 there are no queries
--   - encoding: any unknown distribution D on a finite domain U → ∀ X with Fintype X, ∀ P : PMF X; the mechanism is chosen after X and before P; reason: same quantifiers
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Theorem 3.8, p.25 (continued on p.26); formal version of Theorem 1.2, p.4

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_RandMechanism
import Definitions.Def_HierADA_failureProb

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Theorem 3.8 (Accurate answers to adaptive queries)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Theorem 3.8, pp.25–26 (the formal version of Theorem 1.2, p.4).

There is a universal constant `C` such that for every accuracy `α ∈ (0, 1)`, failure probability
`ξ ∈ (0, 1)` and number of queries `k`, there are a sample size
`N ≤ C (√k/α + 1/α²) log⁵(k/(αξ))` and a seed probability space such that, for every finite domain
`X`, some randomized mechanism on `N` samples satisfies: for every distribution `P` on `X` and every
adaptive analyst, with probability at least `1 − ξ` over the sample and the seed, all `k` answers
satisfy `|a_t − E_{X∼P} f_t(X)| ≤ α`.

**Formalization Note.** O(·) is one constant `C` chosen before `α, ξ, k`. The sample size and the
seed space are chosen before the domain; the mechanism may depend on the domain but never on `P`.
Analysts are deterministic maps from the history to the next query (published `Analyst`); the
interaction, the population mean and the error event are those of `IsRandomnessNecessaryADA.Plain`.
`log` is the natural logarithm. The failure event is required to be measurable in the seed, so that
its probability is defined. **Correction:** the printed "any accuracy parameter `α > 0`" is
restricted to `α ∈ (0, 1)` (the range of Theorem 1.2): for `α > k/ξ` the factor `log⁵(k/(αξ))` is
negative and no `N` exists (`k = 1`, `ξ = 1/2`, `α = 4`). -/
theorem theorem_3_8 :
    ∃ C : ℝ, ∀ α ξ : ℝ, 0 < α → α < 1 → 0 < ξ → ξ < 1 → ∀ k : ℕ,
      ∃ N : ℕ, (N : ℝ) ≤ C * (Real.sqrt k / α + 1 / α ^ 2) * Real.log (k / (α * ξ)) ^ 5 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
        ∀ (X : Type) [Fintype X], ∃ M : RandMechanism Ω X N,
          (∀ (P : PMF X) (A : Analyst X) (s : Fin N → X),
            MeasurableSet {ω | interaction (M ω) A s k ∈ errorEvent P α}) ∧
          ∀ (P : PMF X) (A : Analyst X), failureProb μ M P A α k ≤ ENNReal.ofReal ξ := by sorry

end HierADA
