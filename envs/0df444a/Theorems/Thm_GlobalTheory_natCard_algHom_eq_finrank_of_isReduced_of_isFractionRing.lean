-- Prove2me | Theorems.Thm_GlobalTheory_natCard_algHom_eq_finrank_of_isReduced_of_isFractionRing
-- name    : GlobalTheory.natCard_algHom_eq_finrank_of_isReduced_of_isFractionRing
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:21.814802+00:00
-- url     : https://prove2.me/theorems/90d37017-8f09-5f84-adf1-43dbf615cfd0
-- title:
--   Global Theory: nat Card alg Hom eq finrank of is Reduced of is Fraction Ring
-- statement:
--   The Global Theory construction uses the nat Card alg Hom eq finrank of is Reduced of is Fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L231-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L231-L243

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable (R S L : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field L] [Algebra R L]

theorem GlobalTheory.natCard_algHom_eq_finrank_of_isReduced_of_isFractionRing [Module.Free R S]
    [Module.Finite R S] [IsReduced S] (K : Type*) [Field K] [PerfectField K] [Algebra R K]
    [IsFractionRing R K] [Algebra K L] [IsScalarTower R K L] [IsSepClosed L] :
    Nat.card (S →ₐ[R] L) = finrank R S := by sorry
