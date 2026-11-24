-- Prove2me | Theorems.Thm_GlobalTheory_identityComponent_shear_mul
-- name    : GlobalTheory.identityComponent_shear_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:00.710182+00:00
-- url     : https://prove2.me/theorems/7f12c8a4-e29e-4d2f-bde5-b5cbe68b8585
-- title:
--   Global Theory: identity Component shear mul
-- statement:
--   The Global Theory construction uses the identity Component shear mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIdentityComponentsOfMulInv.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIdentityComponentsOfMulInv.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityComponentsSmoothGroupSchemeMulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvMemConnectedComponentInFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIdentityComponentsOfMulInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.identityComponent_shear_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = snd G G := by sorry
