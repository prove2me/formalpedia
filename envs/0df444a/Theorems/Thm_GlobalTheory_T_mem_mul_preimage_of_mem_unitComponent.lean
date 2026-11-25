-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_mul_preimage_of_mem_unitComponent
-- name    : GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:35:42.215349+00:00
-- url     : https://prove2.me/theorems/879b72ab-22d5-4c8e-a12b-b90cc8af6383
-- title:
--   T: mem mul preimage of mem unit Component
-- statement:
--   The T construction uses the mem mul preimage of mem unit Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemUnitComponentMulMemStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemUnitComponentMulMemStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMemStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_mul_preimage_of_mem_unitComponent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (η[G]).left (G.hom y) ∈ U → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by sorry
