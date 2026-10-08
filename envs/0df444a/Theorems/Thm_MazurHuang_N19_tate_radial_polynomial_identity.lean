-- Prove2me | Theorems.Thm_MazurHuang_N19_tate_radial_polynomial_identity
-- name    : MazurHuang.N19.tate_radial_polynomial_identity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-07T18:12:57.058652+00:00
-- url     : https://prove2.me/theorems/bc3426f4-c1a0-4bf0-8833-762e43e76c94
-- title:
--   Radial normalization of the Tate polynomial
-- statement:
--   Under b=rc, the Tate polynomial has the common factor c¹⁵. The displayed residual polynomial has degree at most nine in c.
-- source:
--   Apache-2.0; fork 51bbb4f191ad0d3753b87123635c100a638ae580; FLT/Assumptions/MazurProof/TateNFDivision.lean:139-221

import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial

theorem MazurHuang.N19.tate_radial_polynomial_identity (r c : ℚ) : MazurProof.TateNFDivision.F19 (r*c) c = c^15 * (fun (r c : ℚ) =>
      r^5*(r-1)^10
      - r*(r-1)^9*(20*r^3-15*r^2+6*r-1)*c
      + 3*r*(r-1)^8*(23*r^3-12*r^2+5*r-1)*c^2
      - r*(r-1)^6*(121*r^4-144*r^3+41*r^2-25*r+6)*c^3
      + r*(r-1)^5*(105*r^4-60*r^3-30*r^2-31*r+10)*c^4
      - 3*r*(r-1)^4*(16*r^4+3*r^3-7*r^2-22*r+5)*c^5
      + (r-1)^3*(11*r^5+12*r^4+3*r^3-50*r^2+3*r+1)*c^6
      - r^2*(r-1)^2*(r^3+2*r^2+3*r-21)*c^7
      - 6*r^2*(r-1)*c^8 + r^2*c^9) r c := by sorry
