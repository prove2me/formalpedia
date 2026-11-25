-- Prove2me | Theorems.Thm_GlobalTheory_isSmoothAt_of_flat_of_finrank_cotangent_le
-- name    : GlobalTheory.isSmoothAt_of_flat_of_finrank_cotangent_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:42:59.358219+00:00
-- url     : https://prove2.me/theorems/4635e5f0-cd35-52bc-b4d4-88cb27271c1e
-- title:
--   Global Theory: is Smooth At of flat of finrank cotangent le
-- statement:
--   The Global Theory construction uses the is Smooth At of flat of finrank cotangent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L586-L597
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L586-L597

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
variable (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [PerfectField (ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
  {A : Type u} [CommRing A] [Algebra V A] [Algebra.FiniteType V A] [Module.Flat V A]

theorem GlobalTheory.isSmoothAt_of_flat_of_finrank_cotangent_le {ϖ : V} (hϖ : Irreducible ϖ) {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), ringKrullDim ((K ⊗[V] A) ⧸ p) = d)
    (x : Ideal (A ⧸ Ideal.span {algebraMap V A ϖ})) [x.IsMaximal]
    (hx : Module.finrank ((A ⧸ Ideal.span {algebraMap V A ϖ}) ⧸ x) x.Cotangent ≤ d) :
    Algebra.IsSmoothAt V (x.comap (Ideal.Quotient.mk _)) ∧
      (∃ f ∉ x.comap (Ideal.Quotient.mk _),
        Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f)) ∧
      IsRegularLocalRing (Localization.AtPrime x) ∧ ringKrullDim (Localization.AtPrime x) = d ∧
      Module.finrank ((A ⧸ Ideal.span {algebraMap V A ϖ}) ⧸ x) x.Cotangent = d := by sorry
