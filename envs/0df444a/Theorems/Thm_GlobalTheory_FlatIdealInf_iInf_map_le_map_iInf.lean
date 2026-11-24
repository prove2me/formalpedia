-- Prove2me | Theorems.Thm_GlobalTheory_FlatIdealInf_iInf_map_le_map_iInf
-- name    : GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:45.776409+00:00
-- url     : https://prove2.me/theorems/f73db297-c8ab-4b7d-89f4-ea0ba08554e6
-- title:
--   Flat Ideal Inf: i Inf map le map i Inf
-- statement:
--   The Flat Ideal Inf construction uses the i Inf map le map i Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlat.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IInfMapLeMapIInfOfFlat.lean#L54-L66

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

theorem GlobalTheory.FlatIdealInf.iInf_map_le_map_iInf : ∀ {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    [Module.Flat B R] {ι : Type} [Finite ι] (K : ι → Ideal B),
    ⨅ i, (K i).map (algebraMap B R) ≤ (⨅ i, K i).map (algebraMap B R) := by sorry
