-- Prove2me | Theorems.Thm_GlobalTheory_exists_affine_chart_of_isPullback
-- name    : GlobalTheory.exists_affine_chart_of_isPullback
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:43:25.643293+00:00
-- url     : https://prove2.me/theorems/3a3a8caa-832d-41bb-839d-ccf87ab1884e
-- title:
--   Global Theory: exists affine chart of is Pullback
-- statement:
--   The Global Theory construction uses the exists affine chart of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L633-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L633-L647

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

theorem GlobalTheory.exists_affine_chart_of_isPullback {O k : Type u} [CommRing O] [CommRing k] [Algebra O k]
    {X X₀ : Scheme.{u}} {f : X ⟶ Spec (.of O)} {i : X₀ ⟶ X} {p : X₀ ⟶ Spec (.of k)}
    (h : IsPullback i p f (Spec.map (CommRingCat.ofHom (algebraMap O k))))
    {A : Type u} [CommRing A] [Algebra O A] (j : Spec (.of A) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A))) :
    ∃ (j₀ : Spec (.of (k ⊗[O] A)) ⟶ X₀) (_ : IsOpenImmersion j₀),
      IsPullback j₀ (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[O] k ⊗[O] A).toRingHom)) i j := by sorry
