-- Prove2me | Theorems.Thm_GeneralCK_Certificates_checkLog_sound
-- name    : GeneralCK.Certificates.checkLog_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T20:49:04.085341+00:00
-- url     : https://prove2.me/theorems/eaa8c4b3-b684-48e2-974c-1c7cf7e88f4c
-- title:
--   Soundness of the rational logarithm interval checker
-- statement:
--   Let $w,\ell,u\in\mathbb Q$ and $n\in\mathbb N$. If the rational logarithm checker checkLog accepts $(w,n,\ell,u)$, then $$\ell\le\log\!\left(\frac{1+w}{1-w}\right)\le u.$$ The checker verifies $0\le w<1$ and encloses a finite odd-power series together with a proved Taylor remainder. Rational inputs and bounds are cast to real numbers in the conclusion, and $\log$ is the natural logarithm. This theorem turns finite exact checker results into analytic logarithm bounds for the Courtade–Kumar certificates.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/LogBounds.lean#L22-L43

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_LogBounds

open GeneralCK.Certificates
open scoped BigOperators

theorem GeneralCK.Certificates.checkLog_sound {w lo hi : ℚ} {n : ℕ}
    (hc : checkLog w n lo hi = true) :
    (lo : ℝ) ≤ Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ∧
    Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ≤ (hi : ℝ) := by sorry
