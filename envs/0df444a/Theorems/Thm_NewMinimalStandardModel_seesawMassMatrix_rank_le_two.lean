-- Prove2me | Theorems.Thm_NewMinimalStandardModel_seesawMassMatrix_rank_le_two
-- name    : NewMinimalStandardModel.seesawMassMatrix_rank_le_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-04T12:16:23.376518+00:00
-- url     : https://prove2.me/theorems/e88b953c-95c7-43b2-9bd1-02b4670a352d
-- title:
--   Two right-handed neutrinos: the seesaw mass matrix has rank $\le 2$ and a massless state
-- statement:
--   Let $v\in\mathbb R$, let $h_\nu$ be a complex $2\times3$ Yukawa matrix and let $M_1,M_2>0$ be the right-handed-neutrino masses. Let $m_D = h_\nu v/\sqrt2$ and let
--   $$m_\nu = -\,m_D^{\mathsf T}\operatorname{diag}(M_1,M_2)^{-1}m_D$$
--   be the seesaw light-neutrino mass matrix. Then
--
--   1. $\operatorname{rank} m_\nu \le 2$, and
--   2. some physical mass of $m_\nu$ vanishes: $\sigma_i(m_\nu)=0$ for some $i$, where $\sigma_i(m_\nu)=\sqrt{\lambda_i(m_\nu^\dagger m_\nu)}$.
--
--   This is the statement "Because the left-handed neutrino Majorana mass matrix has rank two, there is one massless state" (p. 119).
-- source:
--   H. Davoudiasl, R. Kitano, T. Li, H. Murayama, The new Minimal Standard Model, Phys. Lett. B 609 (2005) 117-123, https://doi.org/10.1016/j.physletb.2005.01.026, p. 119, right column (discussion after Eq. (4))

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

namespace NewMinimalStandardModel

theorem seesawMassMatrix_rank_le_two (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) :
    (seesawMassMatrix v hν M).rank ≤ 2 ∧
      ∃ i, majoranaMasses (seesawMassMatrix v hν M) i = 0 := by sorry

end NewMinimalStandardModel
