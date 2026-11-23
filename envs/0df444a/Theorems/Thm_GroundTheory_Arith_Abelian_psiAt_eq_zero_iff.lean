-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_psiAt_eq_zero_iff
-- name    : GroundTheory.Arith.Abelian.psiAt_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:07.231701+00:00
-- url     : https://prove2.me/theorems/c3c18d85-226f-4013-be18-a6a548b99792
-- title:
--   Abelian: psi At eq zero iff
-- statement:
--   The Abelian construction uses the psi At eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L547-L548
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L547-L548

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
  {x₀ y₀ : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
omit [DecidableEq F]
include h₀

theorem GroundTheory.Arith.Abelian.psiAt_eq_zero_iff (n : ℤ) : psiAt W x₀ y₀ n = 0 ↔ (W.ΨSq n).eval x₀ = 0 := by sorry
