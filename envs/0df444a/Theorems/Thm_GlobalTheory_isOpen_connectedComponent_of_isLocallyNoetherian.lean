-- Prove2me | Theorems.Thm_GlobalTheory_isOpen_connectedComponent_of_isLocallyNoetherian
-- name    : GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:05.284116+00:00
-- url     : https://prove2.me/theorems/296196ce-c164-4970-84ee-398929df3123
-- title:
--   Global Theory: is Open connected Component of is Locally Noetherian
-- statement:
--   The Global Theory construction uses the is Open connected Component of is Locally Noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenConnectedComponentOfIsLocallyNoetherian.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenConnectedComponentOfIsLocallyNoetherian.lean#L34-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherian
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
set_option autoImplicit false

theorem GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by sorry
