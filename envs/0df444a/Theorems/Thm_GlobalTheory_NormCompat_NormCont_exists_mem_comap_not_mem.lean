-- Prove2me | Theorems.Thm_GlobalTheory_NormCompat_NormCont_exists_mem_comap_not_mem
-- name    : GlobalTheory.NormCompat.NormCont.exists_mem_comap_not_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:34:21.922133+00:00
-- url     : https://prove2.me/theorems/6e0625cd-0acf-45e4-9fe1-73047426ab47
-- title:
--   Norm Cont: exists mem comap not mem
-- statement:
--   The Norm Cont construction uses the exists mem comap not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormCloseToOneOfCloseAbovePlace.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormCloseToOneOfCloseAbovePlace.lean#L68-L75

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem GlobalTheory.NormCompat.NormCont.exists_mem_comap_not_mem (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K))
    (hw : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) :
    ∃ e : 𝓞 E, algebraMap (𝓞 E) (𝓞 K) e ∈ w.asIdeal ∧ e ∉ v.asIdeal := by sorry
