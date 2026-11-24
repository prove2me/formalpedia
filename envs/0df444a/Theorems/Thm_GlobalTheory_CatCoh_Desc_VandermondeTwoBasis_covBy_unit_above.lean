-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_VandermondeTwoBasis_covBy_unit_above
-- name    : GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:13:46.862105+00:00
-- url     : https://prove2.me/theorems/2ff2756e-7742-4da0-8f82-ccbfacf2fdb2
-- title:
--   Vandermonde Two Basis: cov By unit above
-- statement:
--   The Vandermonde Two Basis construction uses the cov By unit above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisObjectsUnitLociCoverAbove.lean#L85-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BasisObjectsUnitLociCoverAbove.lean#L85-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisObjectsUnitLociCoverAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential

theorem GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → _root_.GlobalTheory.CatCoh.Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (t : C') (u : T ⟶ G.obj t), _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), (∃ i, IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ G.map a) (d i))) ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) := by sorry
