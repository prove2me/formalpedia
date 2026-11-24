-- Prove2me | Theorems.Thm_GlobalTheory_StabFlat_flat_of_regular
-- name    : GlobalTheory.StabFlat.flat_of_regular
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:30.037878+00:00
-- url     : https://prove2.me/theorems/5744ec77-f670-4d73-b4e8-4bde751d38f4
-- title:
--   Stab Flat: flat of regular
-- statement:
--   The Stab Flat construction uses the flat of regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/LocalizationOfIsStandardSmooth.lean#L10-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocalizationOfIsStandardSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.StabFlat

theorem GlobalTheory.StabFlat.flat_of_regular {V C : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] {ϖ : V}
    (hϖ : Irreducible ϖ) (σ : V →+* C) (h : IsSMulRegular C (σ ϖ)) : σ.Flat := by sorry
