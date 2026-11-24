-- Prove2me | Theorems.Thm_GlobalTheory_mem_identityComponents_of_mul_inv
-- name    : GlobalTheory.mem_identityComponents_of_mul_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:20.493831+00:00
-- url     : https://prove2.me/theorems/6893f2f5-76de-4414-8339-e5be12a42644
-- title:
--   Global Theory: mem identity Components of mul inv
-- statement:
--   The Global Theory construction uses the mem identity Components of mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIdentityComponentsOfMulInv.lean#L15-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIdentityComponentsOfMulInv.lean#L15-L34

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

theorem GlobalTheory.mem_identityComponents_of_mul_inv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by sorry
