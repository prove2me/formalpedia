-- Prove2me | Theorems.Thm_GlobalTheory_TraceSpread_finrank_iff_trace
-- name    : GlobalTheory.TraceSpread.finrank_iff_trace
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:11:20.35007+00:00
-- url     : https://prove2.me/theorems/b98cf1aa-fac3-432a-b235-9b80284eeb83
-- title:
--   Trace Spread: finrank iff trace
-- statement:
--   The Trace Spread construction uses the finrank iff trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmTypeEigenMultiplicityOfDensePrimes.lean#L129-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmTypeEigenMultiplicityOfDensePrimes.lean#L129-L206

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmTypeEigenMultiplicityOfDensePrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TraceSpread
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]

theorem GlobalTheory.TraceSpread.finrank_iff_trace (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) {K : Type} [Field K]
    [IsAlgClosed K] [CharZero K] {V : Type}
    [AddCommGroup V] [Module K V] [Module.Finite K V] (ρ : 𝓞 E →+* Module.End K V) (s : K)
    (hs : s ^ 2 = -(H.d : K)) :
    (∀ τ : 𝓞 E →+* K, (τ H.rt = s → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ τ) = p) ∧
      (τ H.rt ≠ s → Module.finrank K (_root_.GlobalTheory.EigenSplit.eigenSub ρ τ) = q)) ↔
    ∀ a, 2 * s * LinearMap.trace K V (ρ a) =
      (p + q) * s * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K) +
      (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : K) := by sorry
