-- Prove2me | Theorems.Thm_GlobalTheory_image_connectedComponent_of_isEmbedding
-- name    : GlobalTheory.image_connectedComponent_of_isEmbedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:07.560226+00:00
-- url     : https://prove2.me/theorems/331f4e28-b000-4c7c-8ba2-9f9576eca6b4
-- title:
--   Global Theory: image connected Component of is Embedding
-- statement:
--   The Global Theory construction uses the image connected Component of is Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComponentInFibreIffOfIsPullback.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComponentInFibreIffOfIsPullback.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullback
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

theorem GlobalTheory.image_connectedComponent_of_isEmbedding {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : Topology.IsEmbedding q) (a : A) :
    q '' connectedComponent a = connectedComponentIn (Set.range q) (q a) := by sorry
