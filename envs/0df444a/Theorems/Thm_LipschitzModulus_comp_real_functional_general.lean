-- Prove2me | Theorems.Thm_LipschitzModulus_comp_real_functional_general
-- name    : LipschitzModulus.comp_real_functional_general
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:25.260656+00:00
-- url     : https://prove2.me/theorems/f9dc6c73-fa2e-4bf7-be8c-127a62dc6eeb
-- title:
--   Lipschitz modulus under precomposition by a real linear functional
-- statement:
--   Let $E$ be a real normed vector space, $f:\mathbb R\to\mathbb R$ a Lipschitz function, and $\phi:E\to\mathbb R$ a continuous linear functional. Then the optimal Lipschitz modulus satisfies
--   $$\operatorname{Lip}(f\circ\phi)=\operatorname{Lip}(f)\,\|\phi\|.$$
--   Here the modulus is the extended nonnegative supremum of secant slopes and $\|\phi\|$ is the operator norm. The result includes the zero functional and does not require norm attainment or finite-dimensionality. This extracts the auxiliary result `RegMTProof.modulus_comp` from the accepted solution of Theorem 3.1(ii), by Prove2me contributor `sometik179` (submission `c137b972-b60a-4d9e-9e5f-2c13f3596d16`), into a separately importable theorem.
-- source:
--   Shafieezadeh-Abadeh, Kuhn and Mohajerin Esfahani, Regularization via Mass Transportation, https://arxiv.org/abs/1710.10016, Theorem 3.1(ii), p. 8; formal helper by sometik179, Prove2me accepted submission c137b972-b60a-4d9e-9e5f-2c13f3596d16.

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_lipschitzModulus

open scoped NNReal

namespace LipschitzModulus

theorem comp_real_functional_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ) (hf : ∃ K : ℝ≥0, LipschitzWith K f)
    (φ : E →L[ℝ] ℝ) :
    WassersteinDRO.Duality.lipschitzModulus (fun x => f (φ x)) =
      WassersteinDRO.Duality.lipschitzModulus f * ENNReal.ofReal ‖φ‖ := by sorry

end LipschitzModulus
