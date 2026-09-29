-- Prove2me | Theorems.Thm_Leptogenesis_lightMassMatrix_diagonalization
-- name    : Leptogenesis.lightMassMatrix_diagonalization
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:33:11.406353+00:00
-- url     : https://prove2.me/theorems/9b42d754-f27f-4922-96da-f8558ef5cc66
-- title:
--   Diagonalization $m=U^*D_mU^\dagger$ of the seesaw light-neutrino mass matrix (Eq. 2.6)
-- statement:
--   Let $v>0$, let $M_1,M_2,M_3>0$ and let $\lambda$ be any complex $3\times3$ Yukawa matrix. Then the light-neutrino mass matrix $[m]_{\alpha\beta}=\sum_k\lambda_{\alpha k}M_k^{-1}\lambda_{\beta k}v^2$ of Eq. (2.5) can be diagonalized as in Eq. (2.6): there exist a unitary $3\times3$ matrix $U$ and real numbers $m_1,m_2,m_3\ge0$ with $$[m]=U^*D_mU^\dagger,\qquad D_m=\operatorname{diag}(m_1,m_2,m_3).$$
-- source:
--   S. Davidson, E. Nardi, Y. Nir, Leptogenesis, Physics Reports 466 (2008) 105–177, https://doi.org/10.1016/j.physrep.2008.06.002, Sec. 2.1, Eq. (2.6) (p. 111)

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

open Matrix

namespace Leptogenesis

/-- Eq. (2.6): the light-neutrino mass matrix can be diagonalized as `m = U^* D_m U^†`. -/
theorem lightMassMatrix_diagonalization (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ)
    (hM : ∀ k, 0 < M k) (lam : Matrix (Fin 3) (Fin 3) ℂ) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ) (masses : Fin 3 → ℝ),
      IsLightMassDiagonalization (lightMassMatrix v M lam) U masses := by sorry

end Leptogenesis
