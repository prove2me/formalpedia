-- Prove2me | Theorems.Thm_GlobalTheory_FlatIdealInf_mem_map_algebraMap_iff
-- name    : GlobalTheory.FlatIdealInf.mem_map_algebraMap_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:38.958672+00:00
-- url     : https://prove2.me/theorems/3be91bdf-0f86-4985-89ef-58bbd1944d40
-- title:
--   Flat Ideal Inf: mem map algebra Map iff
-- statement:
--   The Flat Ideal Inf construction uses the mem map algebra Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlat.lean#L41-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlat.lean#L41-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IInfMapLeMapIInfOfFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatIdealInf
open TensorProduct

theorem GlobalTheory.FlatIdealInf.mem_map_algebraMap_iff {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (I : Ideal B) (x : R) :
    x ∈ I.map (algebraMap B R) ↔
      x ⊗ₜ[B] (1 : B) ∈ LinearMap.range (LinearMap.lTensor R (Submodule.subtype (I.restrictScalars B))) := by sorry
