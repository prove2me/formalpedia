-- Prove2me | Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
-- name    : GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:17.794797+00:00
-- url     : https://prove2.me/theorems/3f91f131-f21e-4b19-ac3f-481f15b127fc
-- title:
--   Global Theory: is Domain and is Integrally Closed of is Regular Local Ring
-- statement:
--   The Global Theory construction uses the is Domain and is Integrally Closed of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L141-L145

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

theorem GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by sorry
