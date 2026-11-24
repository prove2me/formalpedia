-- Prove2me | Theorems.Thm_GlobalTheory_ClopenIdealSheaf_map_comap_localization
-- name    : GlobalTheory.ClopenIdealSheaf.map_comap_localization
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:21.398882+00:00
-- url     : https://prove2.me/theorems/49bebad3-fcff-4f82-a1f3-7d4b73faad34
-- title:
--   Clopen Ideal Sheaf: map comap localization
-- statement:
--   The Clopen Ideal Sheaf construction uses the map comap localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSheafDataOfIsClopenFamily.lean#L9-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSheafDataOfIsClopenFamily.lean#L9-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSheafDataOfIsClopenFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.ClopenIdealSheaf

theorem GlobalTheory.ClopenIdealSheaf.map_comap_localization {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra A T] (f : R) [IsLocalization.Away f S] (ρ : R →+* A)
    [IsLocalization.Away (ρ f) T] (τ : S →+* T)
    (hcomm : ∀ a, τ (algebraMap R S a) = algebraMap A T (ρ a)) (I : Ideal A) :
    (I.comap ρ).map (algebraMap R S) = (I.map (algebraMap A T)).comap τ := by sorry
