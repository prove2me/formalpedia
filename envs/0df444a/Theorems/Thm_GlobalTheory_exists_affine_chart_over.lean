-- Prove2me | Theorems.Thm_GlobalTheory_exists_affine_chart_over
-- name    : GlobalTheory.exists_affine_chart_over
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:24.863818+00:00
-- url     : https://prove2.me/theorems/36ebee1e-61e8-47c2-9ce3-0797d0edcbc8
-- title:
--   Global Theory: exists affine chart over
-- statement:
--   The Global Theory construction uses the exists affine chart over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L619-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SpanFinrankMaximalIdealLeNcardOfLeSupSq.lean#L619-L631

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

theorem GlobalTheory.exists_affine_chart_over {O : Type u} [CommRing O] {X : Scheme.{u}} (f : X ⟶ Spec (.of O))
    (x : X) : ∃ (A : Type u) (_ : CommRing A) (_ : Algebra O A) (j : Spec (.of A) ⟶ X)
      (_ : IsOpenImmersion j) (q : PrimeSpectrum A), j q = x ∧
      j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)) := by sorry
