-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_VandermondeTwoBasis_coboundary_on_piece
-- name    : GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:48:18.576034+00:00
-- url     : https://prove2.me/theorems/07636e11-9433-46e1-ac40-462b4cd0cc5b
-- title:
--   Vandermonde Two Basis: coboundary on piece
-- statement:
--   The Vandermonde Two Basis construction uses the coboundary on piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoCocycleCoboundaryOnUnitLocusPiece.lean#L14-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TwoCocycleCoboundaryOnUnitLocusPiece.lean#L14-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CovBy
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfUpwardFamilyStandardCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGluedSectionUpwardFamilyStandardCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleUpwardFamilyIsCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwoCocycleCoboundaryOnUnitLocusPiece
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory.CatCoh
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
open Classical

theorem GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by sorry
