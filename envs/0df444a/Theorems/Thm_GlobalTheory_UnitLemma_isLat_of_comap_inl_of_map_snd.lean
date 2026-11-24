-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_isLat_of_comap_inl_of_map_snd
-- name    : GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:37:50.179801+00:00
-- url     : https://prove2.me/theorems/b3223c18-e4db-4cf7-9c5e-6fd528a1e677
-- title:
--   Unit Lemma: is Lat of comap inl of map snd
-- statement:
--   The Unit Lemma construction uses the is Lat of comap inl of map snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeProdOfComapInlMapSnd.lean#L8-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeProdOfComapInlMapSnd.lean#L8-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A))
    (h₁ : IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)))
    (h₂ : IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A))) : IsLat K.O K.E M := by sorry
