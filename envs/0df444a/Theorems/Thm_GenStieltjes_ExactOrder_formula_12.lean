-- Prove2me | Theorems.Thm_GenStieltjes_ExactOrder_formula_12
-- name    : GenStieltjes.ExactOrder.formula_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:00.098173+00:00
-- url     : https://prove2.me/theorems/194044ff-82e7-43ad-b84c-933917f45a3e
-- title:
--   Formula (12) — $\frac{1}{(u+z)^\alpha}=\frac{\Gamma(\beta)}{\Gamma(\alpha)\Gamma(\beta-\alpha)}\int_0^\infty\frac{t^{\beta-\alpha-1}\,dt}{(z+u+t)^\beta}$
-- statement:
--   Let $0<\alpha<\beta$, $z>0$ and $u\ge 0$. Then the function $t\mapsto t^{\beta-\alpha-1}(z+u+t)^{-\beta}$ is Lebesgue integrable on $(0,\infty)$, and
--   $$\frac{1}{(u+z)^\alpha}=\frac{\Gamma(\beta)}{\Gamma(\alpha)\Gamma(\beta-\alpha)}\int_{(0,\infty)}\frac{t^{\beta-\alpha-1}\,dt}{(z+u+t)^\beta}.$$
--
--   This Beta-integral identity rewrites the kernel of $S_\alpha$ as a superposition of kernels of $S_\beta$; it is the identity from which the inclusion $S_\alpha\subset S_\beta$ and the explicit measure (10) of Theorem 3 are derived.
--
--   **Formalization Note** The identity is stated for real $z>0$, the case used by the mission's representation on $(0,\infty)$. Integrability is part of the conclusion, so the Bochner integral cannot take its junk value $0$.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, p. 4, formula (12) (proof of Theorem 3)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
import Definitions.Def_GenStieltjes_ExactOrder_Basic

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Formula (12), p. 4 (proof of Theorem 3): for `0 < α < β`, `z > 0` and `u ≥ 0`,
`1/(u + z)^α = Γ(β)/(Γ(α)Γ(β − α)) ∫_{(0,∞)} t^{β−α−1} dt / (z + u + t)^β`,
the integrand being Lebesgue integrable on `(0, ∞)`. -/
theorem formula_12 (α β z u : ℝ) (hα : 0 < α) (hαβ : α < β) (hz : 0 < z) (hu : 0 ≤ u) :
    MeasureTheory.IntegrableOn
        (fun t : ℝ => t ^ (β - α - 1) / (z + u + t) ^ β) (Set.Ioi 0) ∧
      1 / (u + z) ^ α =
        Real.Gamma β / (Real.Gamma α * Real.Gamma (β - α)) *
          ∫ t in Set.Ioi (0 : ℝ), t ^ (β - α - 1) / (z + u + t) ^ β := by sorry

end GenStieltjes.ExactOrder
