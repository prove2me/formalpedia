-- Prove2me | Theorems.Thm_GlobalTheory_UnramifiedEmbedding_quotientMap_bijective
-- name    : GlobalTheory.UnramifiedEmbedding.quotientMap_bijective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:53:27.496598+00:00
-- url     : https://prove2.me/theorems/596ac00d-8619-5634-b040-dd504633ef59
-- title:
--   Unramified Embedding: quotient Map bijective
-- statement:
--   The Unramified Embedding construction uses the quotient Map bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RangeLeRangeOfIsUnramifiedAt.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RangeLeRangeOfIsUnramifiedAt.lean#L40-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RangeLeRangeOfIsUnramifiedAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing NumberField
open GlobalTheory GlobalTheory.UnramifiedEmbedding

theorem GlobalTheory.UnramifiedEmbedding.quotientMap_bijective {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [Algebra O S] [Algebra.IsIntegral O S] [IsAlgClosed (ResidueField O)] (M : Ideal S)
    [M.IsMaximal] (hM : M.comap (algebraMap O S) = maximalIdeal O) :
    Function.Bijective (Ideal.quotientMap M (algebraMap O S) hM.ge) := by sorry
