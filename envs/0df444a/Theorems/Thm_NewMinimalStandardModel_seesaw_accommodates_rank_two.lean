-- Prove2me | Theorems.Thm_NewMinimalStandardModel_seesaw_accommodates_rank_two
-- name    : NewMinimalStandardModel.seesaw_accommodates_rank_two
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T12:58:33.246408+00:00
-- url     : https://prove2.me/theorems/9184afda-e814-4017-a441-fe6c81259f84
-- title:
--   Two-right-handed-neutrino seesaw reproduces every rank-$\le 2$ symmetric light mass matrix
-- statement:
--   Let $v>0$ and $M_1, M_2>0$. For every complex symmetric $3\times 3$ matrix $m$ ($m^{\mathsf T}=m$) with $\operatorname{rank} m\le 2$ there is a complex $2\times3$ Yukawa matrix $h_\nu$ such that
--   $$-\,m_D^{\mathsf T}\operatorname{diag}(M_1,M_2)^{-1}m_D = m,\qquad m_D = \frac{v}{\sqrt2}h_\nu .$$
--
--   This makes precise the paper's remark that, with eleven real parameters in Eq. (4) and only seven light-neutrino parameters (two masses, three mixing angles, one Dirac and one Majorana phase), "we have enough parameters to accommodate the current data": every light-neutrino mass matrix with one massless state is realized by the two-right-handed-neutrino seesaw, for any choice of heavy masses.
-- source:
--   H. Davoudiasl, R. Kitano, T. Li, H. Murayama, The new Minimal Standard Model, Phys. Lett. B 609 (2005) 117-123, https://doi.org/10.1016/j.physletb.2005.01.026, p. 119, right column (parameter count after Eq. (4))

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

namespace NewMinimalStandardModel

theorem seesaw_accommodates_rank_two (v : ℝ) (hv : 0 < v) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) (m : Matrix (Fin 3) (Fin 3) ℂ) (hsymm : m.transpose = m)
    (hrank : m.rank ≤ 2) :
    ∃ hν : Matrix (Fin 2) (Fin 3) ℂ, seesawMassMatrix v hν M = m := by sorry

end NewMinimalStandardModel
