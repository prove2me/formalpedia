-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_gamma_le_h
-- name    : NestedLogitVariants.Competitive.gamma_le_h
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:23:03.197855+00:00
-- url     : https://prove2.me/theorems/dfcf56ff-69c6-41b2-a47b-4cf97e9a0d62
-- title:
--   Proof of Theorem 4, p. 16 — h(α) = (1 − α^γ)/(1 − α) ≥ γ for 0 < α < 1 and 0 < γ ≤ 1
-- statement:
--   Let $0 < \gamma \le 1$ and $0 < \alpha < 1$, and define
--
--   $$h(\alpha) = \frac{1 - \alpha^{\gamma}}{1 - \alpha}.$$
--
--   Then $h(\alpha) \ge \gamma$.
--
--   In the proof of Theorem 4, $\gamma = \gamma_i$ and $\alpha = V_i(S^*_i)/V_i(\hat S_i) \in (0,1)$ is the ratio of the nest's preference weights before and after adding a higher-revenue product. The paper argues that $h$ is decreasing in $\alpha$ and that $h(\alpha) \to \gamma_i$ as $\alpha \uparrow 1$; this item states the inequality the proof uses.
--
--   **Formalization Note** Powers with real exponents are `Real.rpow`; $1 - \alpha > 0$, so no division by zero occurs.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 16, proof of Theorem 4

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- Proof of Theorem 4, p. 16: for `0 < γ ≤ 1` and `0 < α < 1`,
`h(α) = (1 − α^γ) / (1 − α) ≥ γ`. -/
theorem gamma_le_h (γ α : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hα0 : 0 < α) (hα1 : α < 1) :
    γ ≤ (1 - α ^ γ) / (1 - α) := by sorry

end NestedLogitVariants.Competitive
