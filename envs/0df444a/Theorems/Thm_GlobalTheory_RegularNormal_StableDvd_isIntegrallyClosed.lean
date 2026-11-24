-- Prove2me | Theorems.Thm_GlobalTheory_RegularNormal_StableDvd_isIntegrallyClosed
-- name    : GlobalTheory.RegularNormal.StableDvd.isIntegrallyClosed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:20:16.475676+00:00
-- url     : https://prove2.me/theorems/016f351c-fd9f-4bde-91c4-30b51380ce38
-- title:
--   Stable Dvd: is Integrally Closed
-- statement:
--   The Stable Dvd construction uses the is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L14-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L14-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open GlobalTheory.RegularNormal

theorem GlobalTheory.RegularNormal.StableDvd.isIntegrallyClosed {A : Type*} [CommRing A] [IsDomain A] (h : StableDvd A) :
    IsIntegrallyClosed A := by sorry
