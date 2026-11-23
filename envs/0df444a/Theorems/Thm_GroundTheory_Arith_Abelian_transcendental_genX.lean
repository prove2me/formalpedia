-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_transcendental_genX
-- name    : GroundTheory.Arith.Abelian.transcendental_genX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:01.323938+00:00
-- url     : https://prove2.me/theorems/f02c27c8-8861-472d-b44e-f66896ad70f9
-- title:
--   Abelian: transcendental gen X
-- statement:
--   The Abelian construction uses the transcendental gen X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
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
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.transcendental_genX : Transcendental F (genX W) := by sorry
