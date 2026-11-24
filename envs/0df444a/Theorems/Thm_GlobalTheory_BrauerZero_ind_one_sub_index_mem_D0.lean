-- Prove2me | Theorems.Thm_GlobalTheory_BrauerZero_ind_one_sub_index_mem_D0
-- name    : GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:03:47.597034+00:00
-- url     : https://prove2.me/theorems/3de9bfa3-1851-4ba5-b9c2-478e080d2ded
-- title:
--   Brauer Zero: ind one sub index mem D0
-- statement:
--   The Brauer Zero construction uses the ind one sub index mem D0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedOneSubIndexMemDegreeOneCharacterDiff.lean#L7-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InducedOneSubIndexMemDegreeOneCharacterDiff.lean#L7-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI GlobalTheory.BrauerZero
open GlobalTheory GlobalTheory.BrauerZero

theorem GlobalTheory.BrauerZero.ind_one_sub_index_mem_D0 {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by sorry
