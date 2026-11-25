-- Prove2me | Theorems.Thm_GlobalTheory_natCard_algHom_eq_finrank_of_etale_tower
-- name    : GlobalTheory.natCard_algHom_eq_finrank_of_etale_tower
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:04.407988+00:00
-- url     : https://prove2.me/theorems/bf29ce0a-5630-4c94-bac9-bb9388d624fe
-- title:
--   Global Theory: nat Card alg Hom eq finrank of etale tower
-- statement:
--   The Global Theory construction uses the nat Card alg Hom eq finrank of etale tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L224-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L224-L229

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

theorem GlobalTheory.natCard_algHom_eq_finrank_of_etale_tower [Module.Free R S] [Module.Finite R S]
    (K : Type*) [Field K] [Algebra R K] [Algebra K L] [IsScalarTower R K L] [IsSepClosed L]
    [Algebra.FormallyEtale K (K ⊗[R] S)] : Nat.card (S →ₐ[R] L) = finrank R S := by sorry
