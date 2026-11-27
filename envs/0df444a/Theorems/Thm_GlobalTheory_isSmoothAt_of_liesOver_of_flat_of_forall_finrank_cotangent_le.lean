-- Prove2me | Theorems.Thm_GlobalTheory_isSmoothAt_of_liesOver_of_flat_of_forall_finrank_cotangent_le
-- name    : GlobalTheory.isSmoothAt_of_liesOver_of_flat_of_forall_finrank_cotangent_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:42:52.281156+00:00
-- url     : https://prove2.me/theorems/8e2148d1-ff36-5cd0-b295-b849bb7faa48
-- title:
--   Global Theory: is Smooth At of lies Over of flat of forall finrank cotangent le
-- statement:
--   The Global Theory construction uses the is Smooth At of lies Over of flat of forall finrank cotangent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L564-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L564-L584

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

theorem GlobalTheory.isSmoothAt_of_liesOver_of_flat_of_forall_finrank_cotangent_le {d : ℕ}
    (hd : ∀ p ∈ minimalPrimes (K ⊗[V] A), (d : WithBot ℕ∞) ≤ ringKrullDim ((K ⊗[V] A) ⧸ p))
    {B : Type*} [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V A))
    (hx : ∀ x : Ideal B, x.IsMaximal → Module.finrank (B ⧸ x) x.Cotangent ≤ d)
    (q : Ideal A) [q.IsPrime] [q.LiesOver (maximalIdeal V)] :
    Algebra.IsSmoothAt V q ∧
      ∃ f ∉ q, Algebra.IsStandardSmoothOfRelativeDimension d V (Localization.Away f) := by sorry
