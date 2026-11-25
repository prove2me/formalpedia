-- Prove2me | Theorems.Thm_GlobalTheory_ChartQF_quasiFinite_of_pointRigid
-- name    : GlobalTheory.ChartQF.quasiFinite_of_pointRigid
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:11.914784+00:00
-- url     : https://prove2.me/theorems/0187bf5b-ec4b-4f06-a2da-c9c4cce2e56c
-- title:
--   Chart QF: quasi Finite of point Rigid
-- statement:
--   The Chart QF construction uses the quasi Finite of point Rigid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L192-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L192-L267

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF

theorem GlobalTheory.ChartQF.quasiFinite_of_pointRigid {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (hb : ξ ≫ σ = spMap b) (hft : ((residue R).comp b).EssFiniteType)
    (hc : ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) →
      (∀ q, (spMap ev ≫ ξ) q = ξ (closedPoint R)) → (∃ P₀ : Sp k₀ ⟶ S, spMap k₀.subtype ≫ P₀ = spMap ev ≫ ξ) →
      (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀) :
    (∀ p : Sp R, ξ p = ξ (closedPoint R) → p = closedPoint R) ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).Finite := by sorry
