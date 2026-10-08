-- Prove2me | Theorems.Thm_ModelRiskOT_WorstProb_lemma_4
-- name    : ModelRiskOT.WorstProb.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:12:57.559068+00:00
-- url     : https://prove2.me/theorems/528aa259-b570-4418-8ee0-43a737bfb7d2
-- title:
--   Lemma 4 — near-optimal plans $\pi_n \in \Phi_{\mu,\delta}$ with $\pi_n(C_n) \ge 1 - 1/n$ and $\pi_n(S \times A) \ge I - 2/n$
-- statement:
--   Let $S$ be a Polish space, $c$ a cost satisfying (A1), $\mu$ a probability measure on $S$, $\delta > 0$, and $A \subseteq S$ a nonempty closed set. Let $I = \sup\{\pi(S \times A) : \pi \in \Phi_{\mu,\delta}\}$ and suppose $\lambda^* \in [0,\infty)$ attains the infimum in (13). Then there exist probability measures $\pi_n \in \Phi_{\mu,\delta}$, $n > 1$, such that for every $n > 1$:
--   1. $\pi_n(C_n) \ge 1 - 1/n$;
--   2. $\displaystyle\int_{(S \times S)\setminus C_n} c\,d\pi_n = 0$;
--   3. $I(\pi_n) := \pi_n(S \times A) \ge I - 2/n$.
--
--   Here $C_n$ is the set of §2.4.1. The plans $\pi_n$ replace a primal optimizer, which need not exist: they are nearly optimal and transport mass only along the near-optimal moves recorded in $C_n$, and Lemma 2 and Theorem 3 are proved by passing to the limit along them.
--
--   **Formalization Note** The sequence is indexed by $n \in \mathbb N$ and the properties are required for $n > 1$. Item 3 is written $I \le \pi_n(S \times A) + 2/n$ in $[0,\infty]$, so that truncated subtraction plays no role. $\pi_n(C_n)$ is the outer measure and the integral over the complement is a lower integral over the restricted measure; $C_n$ is universally measurable, so these are the completion's values.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 11, Lemma 4

import Mathlib
import Definitions.Def_ModelRiskOT_WorstProb_Cset

open MeasureTheory
open scoped ENNReal

namespace ModelRiskOT.WorstProb

/-- Lemma 4, p. 11. Under (A1), for a nonempty closed `A` and `λ* ∈ [0, ∞)` attaining the infimum in
(13), there are `π_n ∈ Φ_{μ,δ}` (`n > 1`) with `π_n(C_n) ≥ 1 − 1/n`, `∫_{(S×S) \ C_n} c dπ_n = 0`
and `I(π_n) = π_n(S × A) ≥ I − 2/n`, where `I = sup {π(S × A) : π ∈ Φ_{μ,δ}}`.
The last inequality is written `I ≤ π_n(S × A) + 2/n` in `[0, ∞]`. -/
theorem lemma_4 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (A : Set S) (hA : IsClosed A) (hAne : A.Nonempty)
    (lamStar : ℝ) (hlam : AttainsInf13 c μ δ A lamStar) :
    ∃ πs : ℕ → Measure (S × S), ∀ n : ℕ, 1 < n →
      πs n ∈ Phi c μ δ ∧
      ENNReal.ofReal (1 - 1 / (n : ℝ)) ≤ πs n (Cset c A lamStar n) ∧
      ∫⁻ p in (Cset c A lamStar n)ᶜ, ENNReal.ofReal (c p.1 p.2) ∂(πs n) = 0 ∧
      worstProbCoupling c μ δ A ≤ πs n (Set.univ ×ˢ A) + ENNReal.ofReal (2 / (n : ℝ)) := by sorry

end ModelRiskOT.WorstProb
