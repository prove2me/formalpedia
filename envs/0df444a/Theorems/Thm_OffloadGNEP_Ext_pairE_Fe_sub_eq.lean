-- Prove2me | Theorems.Thm_OffloadGNEP_Ext_pairE_Fe_sub_eq
-- name    : OffloadGNEP.Ext.pairE_Fe_sub_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:41:50.714036+00:00
-- url     : https://prove2.me/theorems/f8e6b2b2-b12a-461b-b5db-254cfef4710d
-- title:
--   The extended-game coupling cancels in the monotonicity pairing
-- statement:
--   For any two strategy profiles $x,y$ and any two prices $\rho,\sigma$, the price and utilization terms cancel in the extended VI pairing:
--
--   $$\langle F_e(y,\sigma)-F_e(x,\rho),(y,\sigma)-(x,\rho)\rangle =\langle F(y)-F(x),y-x\rangle.$$
--
--   This identity gives the algebraic content of the skew-symmetric off-diagonal blocks in the Jacobian displayed in the proof of Theorem 2. It works independently of differentiability.
--
--   **Formalization Note** The statement is an identity of total functions, so it needs no load bound; it does not claim that the costs are meaningful at a pole.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 16, proof of Theorem 2, skew-symmetric Jacobian of F_e

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Setting

namespace OffloadGNEP.Ext

/-- The off-diagonal price and utilization terms cancel in the VI pairing. -/
theorem pairE_Fe_sub_eq {N : ℕ} (P : Params N)
    (x y : Fin N → OffloadGNEP.Exist.Tier → ℝ) (ρ σ : ℝ) :
    pairE (Fe P (y, σ) - Fe P (x, ρ)) ((y, σ) - (x, ρ)) =
      OffloadGNEP.Exist.pair (F P y - F P x) (y - x) := by sorry

end OffloadGNEP.Ext
