-- Prove2me | Theorems.Thm_NewMinimalStandardModel_quadratic_chaotic_inflation_predictions
-- name    : NewMinimalStandardModel.quadratic_chaotic_inflation_predictions
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T13:16:58.039199+00:00
-- url     : https://prove2.me/theorems/1bbbfa21-ed5a-470f-91d3-1c5c148226c7
-- title:
--   Quadratic chaotic inflation: $n_s = 1-\frac{4}{2N+1}$ and $r = \frac{16}{2N+1}$
-- statement:
--   Let $m>0$ and $M_{\rm Pl}>0$, and let $V(\varphi)=\tfrac12 m^2\varphi^2$. Let $\varphi_{\rm end}=\sqrt2\,M_{\rm Pl}$, let $\varphi_*>\varphi_{\rm end}$, and let
--   $$N = \frac{1}{M_{\rm Pl}^2}\int_{\varphi_{\rm end}}^{\varphi_*}\frac{V(\psi)}{V'(\psi)}\,d\psi$$
--   be the number of e-folds between $\varphi_*$ and $\varphi_{\rm end}$. Then
--
--   1. $\epsilon(\varphi_{\rm end}) = 1$ (inflation ends at $\varphi_{\rm end}$);
--   2. $n_s(\varphi_*) = 1 - 6\epsilon(\varphi_*) + 2\eta(\varphi_*) = 1-\dfrac{4}{2N+1}$;
--   3. $r(\varphi_*) = 16\,\epsilon(\varphi_*) = \dfrac{16}{2N+1}$;
--   4. if $N = 50$, then $|n_s - 0.96| < 0.005$ and $|r-0.16|<0.005$.
--
--   This is the closed-form content behind the paper's predictions $n_s\simeq 0.96$ and $r\simeq0.16$ for the $\varphi^2$ chaotic inflation model.
--
--   **Formalization Note** The paper quotes the numerical values (citing Ellis–Raidal–Yanagida) without stating the number of e-folds; the value $N=50$ in item 4 is the conventional choice that reproduces them, and items 2–3 hold for every $N$.
-- source:
--   H. Davoudiasl, R. Kitano, T. Li, H. Murayama, The new Minimal Standard Model, Phys. Lett. B 609 (2005) 117-123, https://doi.org/10.1016/j.physletb.2005.01.026, Eq. (5) p. 119 and p. 122 left column ("The spectrum index of the φ² chaotic inflation model is predicted to be 0.96 ... The tensor-to-scalar ratio is 0.16 [21]")

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

namespace NewMinimalStandardModel

theorem quadratic_chaotic_inflation_predictions (m Mpl φstar N : ℝ) (hm : 0 < m)
    (hMpl : 0 < Mpl) (hφ : Real.sqrt 2 * Mpl < φstar)
    (hN : efolds (quadraticPotential m) Mpl (Real.sqrt 2 * Mpl) φstar = N) :
    slowRollEpsilon (quadraticPotential m) Mpl (Real.sqrt 2 * Mpl) = 1 ∧
    spectralIndex (quadraticPotential m) Mpl φstar = 1 - 4 / (2 * N + 1) ∧
    tensorToScalarRatio (quadraticPotential m) Mpl φstar = 16 / (2 * N + 1) ∧
    (N = 50 →
      |spectralIndex (quadraticPotential m) Mpl φstar - 0.96| < 0.005 ∧
      |tensorToScalarRatio (quadraticPotential m) Mpl φstar - 0.16| < 0.005) := by sorry

end NewMinimalStandardModel
