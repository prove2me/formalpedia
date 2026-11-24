-- Prove2me | Theorems.Thm_GlobalTheory_IdCompOpen_isOpen_snd_image
-- name    : GlobalTheory.IdCompOpen.isOpen_snd_image
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:11:57.185898+00:00
-- url     : https://prove2.me/theorems/0f5cf708-a6ae-438a-8df2-79b35815be5a
-- title:
--   Id Comp Open: is Open snd image
-- statement:
--   The Id Comp Open construction uses the is Open snd image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSndImageMulMemOpenGroupScheme.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenSndImageMulMemOpenGroupScheme.lean#L8-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupScheme
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
open GlobalTheory GlobalTheory.IdCompOpen

theorem GlobalTheory.IdCompOpen.isOpen_snd_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens,
    IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by sorry
