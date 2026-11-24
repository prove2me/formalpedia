-- Prove2me | Theorems.Thm_GlobalTheory_T_isFullLattice_prod_of_comap_inl_map_snd
-- name    : GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:09.633154+00:00
-- url     : https://prove2.me/theorems/8e550c2c-8037-4861-b0bd-5f585396bbc2
-- title:
--   T: is Full Lattice prod of comap inl map snd
-- statement:
--   The T construction uses the is Full Lattice prod of comap inl map snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeProdOfComapInlMapSndStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFullLatticeProdOfComapInlMapSndStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSnd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSndStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)) → IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A)) → IsLat K.O K.E M := by sorry
