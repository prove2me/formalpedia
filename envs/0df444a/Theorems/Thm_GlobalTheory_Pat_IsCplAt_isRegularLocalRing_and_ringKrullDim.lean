-- Prove2me | Theorems.Thm_GlobalTheory_Pat_IsCplAt_isRegularLocalRing_and_ringKrullDim
-- name    : GlobalTheory.Pat.IsCplAt.isRegularLocalRing_and_ringKrullDim
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:17:49.024004+00:00
-- url     : https://prove2.me/theorems/0898cab5-1720-45e5-a768-0449dde6a06e
-- title:
--   Is Cpl At: is Regular Local Ring and ring Krull Dim
-- statement:
--   The Is Cpl At construction uses the is Regular Local Ring and ring Krull Dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L314-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsRegularLocalRingOfFlatOfMapEqMaximalIdeal.lean#L314-L331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ProjectionSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing GlobalTheory.Pat CategoryTheory TensorProduct
open GlobalTheory

theorem GlobalTheory.Pat.IsCplAt.isRegularLocalRing_and_ringKrullDim :
    ∀ (R S : Type) [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsLocalRing S] (q : Ideal R)
      [q.IsPrime] (φ : R →+* S), IsCplAt q φ →
      ∃ _ : IsRegularLocalRing S, ringKrullDim S + ringKrullDim (R ⧸ q) = ringKrullDim R := by sorry
