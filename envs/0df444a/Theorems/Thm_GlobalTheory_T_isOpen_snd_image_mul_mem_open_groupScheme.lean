-- Prove2me | Theorems.Thm_GlobalTheory_T_isOpen_snd_image_mul_mem_open_groupScheme
-- name    : GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:49:21.819511+00:00
-- url     : https://prove2.me/theorems/e0cf29b0-5d39-4ec8-973e-c916a0b1fec8
-- title:
--   T: is Open snd image mul mem open group Scheme
-- statement:
--   The T construction uses the is Open snd image mul mem open group Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSndImageMulMemOpenGroupSchemeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSndImageMulMemOpenGroupSchemeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupSchemeStatement
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

theorem GlobalTheory.T.isOpen_snd_image_mul_mem_open_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens, IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by sorry
