-- Prove2me | Theorems.Thm_GlobalTheory_exists_smoothOfRelativeDimension_of_flat_of_forall_finrank_cotangentSpace_le
-- name    : GlobalTheory.exists_smoothOfRelativeDimension_of_flat_of_forall_finrank_cotangentSpace_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:43:03.211597+00:00
-- url     : https://prove2.me/theorems/4e527bde-36c1-5df0-be15-dfcaf0ab9598
-- title:
--   Global Theory: exists smooth Of Relative Dimension of flat of forall finrank cotangent Space le
-- statement:
--   The Global Theory construction uses the exists smooth Of Relative Dimension of flat of forall finrank cotangent Space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L798-L819
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L798-L819

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
open AlgebraicGeometry CategoryTheory Topology
variable (V K k : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [PerfectField (ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
  [Field k] [Algebra V k] (hk : Function.Surjective (algebraMap V k))
  {X X₀ X₁ : Scheme.{u}} {f : X ⟶ Spec (.of V)} [LocallyOfFiniteType f] [Flat f]
  {i₀ : X₀ ⟶ X} {p₀ : X₀ ⟶ Spec (.of k)} {i₁ : X₁ ⟶ X} {p₁ : X₁ ⟶ Spec (.of K)}
  (h₀ : IsPullback i₀ p₀ f (Spec.map (CommRingCat.ofHom (algebraMap V k))))
  (h₁ : IsPullback i₁ p₁ f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
include hk h₀ h₁

theorem GlobalTheory.exists_smoothOfRelativeDimension_of_flat_of_forall_finrank_cotangentSpace_le {d : ℕ}
    (hd : ∀ Z ∈ irreducibleComponents X₁, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z)
    (hx : ∀ x : X₀, IsClosed ({x} : Set X₀) → Module.finrank (ResidueField (X₀.presheaf.stalk x))
      (CotangentSpace (X₀.presheaf.stalk x)) ≤ d) :
    ∃ U : X.Opens, Set.range i₀ ⊆ U ∧ SmoothOfRelativeDimension d (U.ι ≫ f) := by sorry
