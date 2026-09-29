-- Prove2me | Theorems.Thm_Leptogenesis_lightMassMatrix_mulVec_conj_le
-- name    : Leptogenesis.lightMassMatrix_mulVec_conj_le
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:08:00.185296+00:00
-- url     : https://prove2.me/theorems/871435d3-1c30-48c6-9369-fd225e10bae0
-- title:
--   $|m\cdot\hat\ell^*|\le m_{\max}|\hat\ell|$ (Sec. 5.2, below Eq. 5.11)
-- statement:
--   Let $v>0$, $M_k>0$, $\lambda$ a complex $3\times3$ matrix, and $[m]=U^*D_mU^\dagger$ with $U$ unitary and $m_i\ge0$; let $m_{\max}=\max_i m_i$ be the largest light-neutrino mass. Then for every $x\in\mathbb C^3$, $$\big|m\cdot x^*\big|\le m_{\max}\,|x|,$$ where $|\cdot|$ is the Euclidean norm on $\mathbb C^3$ (stated in squared form: $\sum_\alpha|(m\,x^*)_\alpha|^2\le m_{\max}^2\sum_\alpha|x_\alpha|^2$). Applied to the unit vector $\hat\ell_{N_1}$ of Eq. (5.11) this is the inequality $|m\cdot\hat\ell^*_{N_1}|\le|m_{\max}\hat\ell_{N_1}|$ used to derive Eq. (5.10).
-- source:
--   S. Davidson, E. Nardi, Y. Nir, Leptogenesis, Physics Reports 466 (2008) 105–177, https://doi.org/10.1016/j.physrep.2008.06.002, Sec. 5.2, text following Eq. (5.11) (p. 122)

import Mathlib
import Definitions.Def_Leptogenesis_SeesawDefs

open Matrix

namespace Leptogenesis

/-- Sec. 5.2 (below Eq. (5.11)): `|m · x^*| ≤ m_max |x|` for every complex 3-vector `x`. -/
theorem lightMassMatrix_mulVec_conj_le (v : ℝ) (hv : 0 < v) (M : Fin 3 → ℝ)
    (hM : ∀ k, 0 < M k) (lam : Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 3) ℂ)
    (masses : Fin 3 → ℝ)
    (hdiag : IsLightMassDiagonalization (lightMassMatrix v M lam) U masses)
    (x : Fin 3 → ℂ) :
    ∑ α, ‖(lightMassMatrix v M lam *ᵥ star x) α‖ ^ 2 ≤
      (⨆ i, masses i) ^ 2 * ∑ α, ‖x α‖ ^ 2 := by sorry

end Leptogenesis
