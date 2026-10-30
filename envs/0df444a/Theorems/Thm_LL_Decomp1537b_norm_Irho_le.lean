-- Prove2me | Theorems.Thm_LL_Decomp1537b_norm_Irho_le
-- name    : LL_Decomp1537b.norm_Irho_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:32:27.606194+00:00
-- url     : https://prove2.me/theorems/48dc21ff-86b0-4184-b85b-8c9648f8acad
-- title:
--   Trivial bound for the weighted difference sum
-- statement:
--   For all natural numbers $N,N_1$, every integer $h$ and all complex $\rho,\rho'$ with $\operatorname{Re}\rho\le1$ and $\operatorname{Re}\rho'\le1$, one has $|I(h,\rho,\rho')|\le I(h)$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem II, Acta Mathematica Hungarica, 2020; Section 2, display (2.24), p. 5

import Mathlib
import Definitions.Def_LL_Decomp1537b_I1
import Definitions.Def_LL_Decomp1537b_Irho

open Finset Real

namespace LL_Decomp1537b
theorem norm_Irho_le (N N1 : ℕ) (h : ℤ) {ρ ρ' : ℂ} (hρ : ρ.re ≤ 1) (hρ' : ρ'.re ≤ 1) :
    ‖Irho N N1 h ρ ρ'‖ ≤ I1 N N1 h := by sorry
end LL_Decomp1537b
