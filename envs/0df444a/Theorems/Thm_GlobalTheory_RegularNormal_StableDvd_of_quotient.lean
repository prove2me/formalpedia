-- Prove2me | Theorems.Thm_GlobalTheory_RegularNormal_StableDvd_of_quotient
-- name    : GlobalTheory.RegularNormal.StableDvd.of_quotient
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:52.082442+00:00
-- url     : https://prove2.me/theorems/a148270e-95c1-402b-9a7c-2914b02d314b
-- title:
--   Stable Dvd: of quotient
-- statement:
--   The Stable Dvd construction uses the of quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L88-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RegularLocalRingNormalDomain.lean#L88-L104

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
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}

theorem GlobalTheory.RegularNormal.StableDvd.of_quotient (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) :
    StableDvd A := by sorry
