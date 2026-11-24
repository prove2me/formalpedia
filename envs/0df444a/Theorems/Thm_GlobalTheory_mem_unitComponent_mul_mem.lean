-- Prove2me | Theorems.Thm_GlobalTheory_mem_unitComponent_mul_mem
-- name    : GlobalTheory.mem_unitComponent_mul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:29.200399+00:00
-- url     : https://prove2.me/theorems/6cb10d03-6e61-4928-80d2-656db7e499f9
-- title:
--   Global Theory: mem unit Component mul mem
-- statement:
--   The Global Theory construction uses the mem unit Component mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemUnitComponentMulMem.lean#L23-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemUnitComponentMulMem.lean#L23-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMem
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

theorem GlobalTheory.mem_unitComponent_mul_mem :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left),
      (η[G]).left (G.hom y) ∈ U →
      y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} →
      y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by sorry
