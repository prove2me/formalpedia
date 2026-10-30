-- Prove2me | Theorems.Thm_LL_Decomp1537b_Irho_one_one
-- name    : LL_Decomp1537b.Irho_one_one
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:32:53.315669+00:00
-- url     : https://prove2.me/theorems/08094c30-9ed2-4672-b839-8ad2e6cd62b5
-- title:
--   The weighted sum at the pole
-- statement:
--   For all natural numbers $N,N_1$ and every integer $h$, one has $I(h,1,1)=I(h)$.
-- source:
--   J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem II, Acta Mathematica Hungarica, 2020; Section 2, display (2.17), p. 4

import Mathlib
import Definitions.Def_LL_Decomp1537b_I1
import Definitions.Def_LL_Decomp1537b_Irho

open Finset Real

namespace LL_Decomp1537b
theorem Irho_one_one (N N1 : ℕ) (h : ℤ) : Irho N N1 h 1 1 = I1 N N1 h := by sorry
end LL_Decomp1537b
