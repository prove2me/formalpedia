-- Prove2me | Theorems.Thm_GroundTheory_Global_coordEval_mk
-- name    : GroundTheory.Global.coordEval_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:39.901297+00:00
-- url     : https://prove2.me/theorems/483d1541-81f1-4db1-b5cd-2010a877f59e
-- title:
--   Global: coord Eval mk
-- statement:
--   The Global construction uses the coord Eval mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
noncomputable section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsDomain Λ] [IsDiscreteValuationRing Λ]
  [IsLocalHom j]

theorem GroundTheory.Global.coordEval_mk (p : 𝒪[X][Y]) :
    coordEval W j hxy (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom j x) y := by sorry
