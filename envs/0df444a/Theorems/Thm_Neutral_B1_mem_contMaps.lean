-- Prove2me | Theorems.Thm_Neutral_B1_mem_contMaps
-- name    : Neutral.B1.mem_contMaps
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:59.080988+00:00
-- url     : https://prove2.me/theorems/5a44b6fb-a343-55e9-8df6-b0168e63018e
-- title:
--   B1: mem cont Maps
-- statement:
--   The B1 construction uses the mem cont Maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Duality.lean#L35-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
set_option linter.unusedVariables false
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (R M)
variable {R M}

theorem Neutral.B1.mem_contMaps {X : Type*} [TopologicalSpace X] (f : X → M) :
    f ∈ contMaps R M X ↔ Continuous f := by sorry
