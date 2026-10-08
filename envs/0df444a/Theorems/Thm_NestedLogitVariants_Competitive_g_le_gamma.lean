-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_g_le_gamma
-- name    : NestedLogitVariants.Competitive.g_le_gamma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:22:47.297805+00:00
-- url     : https://prove2.me/theorems/47206c04-cc28-451a-9472-4331fb72840d
-- title:
--   Proof of Lemma 3, p. 15 — g(α) = (1 − α^γ)/(α^(γ−1) − α^γ) ≤ γ for 0 < α < 1 and 0 < γ ≤ 1
-- statement:
--   Let $0 < \gamma \le 1$ and $0 < \alpha < 1$, and define
--
--   $$g(\alpha) = \frac{1 - \alpha^{\gamma}}{\alpha^{\gamma - 1} - \alpha^{\gamma}}.$$
--
--   Then $g(\alpha) \le \gamma$.
--
--   In the proof of Lemma 3, $\gamma = \gamma_i$ and $\alpha = V_i(\hat S_i)/V_i(S_i) \in (0,1)$ is the ratio of the nest's preference weights after and before removing a product. The paper argues that $g$ is increasing in $\alpha$ when $\gamma_i \le 1$ and that $g(\alpha) \to \gamma_i$ as $\alpha \uparrow 1$; this item states the inequality that the proof uses.
--
--   **Formalization Note** Powers with real exponents are `Real.rpow`, well defined since $\alpha > 0$. The denominator equals $\alpha^{\gamma-1}(1 - \alpha) > 0$, so no division by zero occurs.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 15, proof of Lemma 3 (last paragraph)

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- Proof of Lemma 3, p. 15: for `0 < γ ≤ 1` and `0 < α < 1`,
`g(α) = (1 − α^γ) / (α^(γ−1) − α^γ) ≤ γ`. -/
theorem g_le_gamma (γ α : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - α ^ γ) / (α ^ (γ - 1) - α ^ γ) ≤ γ := by sorry

end NestedLogitVariants.Competitive
