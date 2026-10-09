-- Prove2me | Theorems.Thm_ModernOnlineLearning_Aggregating_theorem_11_5
-- name    : ModernOnlineLearning.Aggregating.theorem_11_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:32.552234+00:00
-- url     : https://prove2.me/theorems/32564699-e48a-4736-97a1-4978902e0024
-- title:
--   Theorem 11.5, p. 183 — uniform-prior weighted average regret on exp-concave losses
-- statement:
--   Let $V\subseteq\mathbb R^d$ be convex, closed, bounded, and full-dimensional. Let $\alpha>0$, and suppose the losses $\ell_1,\ldots,\ell_T$ are $\alpha$-exp-concave on $V$. The Weighted Average Algorithm starts with the uniform distribution on $V$, sets $\lambda_t=1/\alpha$, and predicts with the exponential-weighted mean $x_t$ of $V$ based on losses before round $t$. For every $u\in V$,
--
--   $$\sum_{t=1}^{T}(\ell_t(x_t)-\ell_t(u))\leq\frac d\alpha\left(1+\ln\left(\frac Td+1\right)\right).$$
--
--   The bound compares one deterministic sequence of weighted predictions with every fixed feasible competitor, with explicit dependence on dimension, horizon, and exp-concavity.
--
--   **Formalization Note** The theorem uses the published EWOO weighted-mean definition, which equals WAA for the uniform prior and $\lambda_t=1/\alpha$. Rounds start at one. The hypotheses $d,T\geq1$, positive volume, almost-everywhere measurability on $V$, and integrability of the exponential weights and their vector moments make the divisions and Bochner integrals represent the source's quantities.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 11.5 and equation (11.6), p. 183; Algorithm 11.1, p. 180

import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint
import Definitions.Def_ModernOnlineLearning_Aggregating_ExpConcave
set_option autoImplicit false

open MeasureTheory

namespace ModernOnlineLearning.Aggregating

/-- Theorem 11.5, p. 183: uniform-prior WAA with `1 / λ_t = α`.
The published EWOO point is exactly the uniform-prior WAA weighted mean. -/
theorem theorem_11_5 {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ V) (hclosed : IsClosed V) (hbounded : Bornology.IsBounded V)
    (hvol_pos : 0 < volume V)
    (α : ℝ) (hα : 0 < α)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hexp : ∀ t ∈ Finset.Icc 1 T, ExpConcaveOn V α (ℓ t))
    (hmeas : ∀ t ∈ Finset.Icc 1 T, AEMeasurable (ℓ t) (volume.restrict V))
    (hint_weight : ∀ t ∈ Finset.Icc 1 T,
      IntegrableOn (LogRegretOCO.EWOO.ewooWeight α ℓ t) V)
    (hint_point : ∀ t ∈ Finset.Icc 1 T,
      IntegrableOn (fun x => LogRegretOCO.EWOO.ewooWeight α ℓ t x • x) V) :
    ∀ u ∈ V,
      (∑ t ∈ Finset.Icc 1 T,
          (ℓ t (LogRegretOCO.EWOO.ewooPoint V α ℓ t) - ℓ t u)) ≤
        (d : ℝ) / α * (1 + Real.log ((T : ℝ) / (d : ℝ) + 1)) := by sorry

end ModernOnlineLearning.Aggregating
