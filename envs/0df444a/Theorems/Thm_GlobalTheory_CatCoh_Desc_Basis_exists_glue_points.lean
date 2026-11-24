-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_exists_glue_points
-- name    : GlobalTheory.CatCoh.Desc.Basis.exists_glue_points
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:14:01.796636+00:00
-- url     : https://prove2.me/theorems/1dc4fc75-cda8-4e10-b25d-10ee5e3d4578
-- title:
--   Basis: exists glue points
-- statement:
--   The Basis construction uses the exists glue points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L51-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L51-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']

theorem GlobalTheory.CatCoh.Desc.Basis.exists_glue_points (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (t₁ t₂ : C') (s : ∀ t, F.obj (G.obj t))
    (hs : ∀ t t' (a : t ⟶ t'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → s t' = mp F (G.map a) (s t)) :
    ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ (x S) = mp F w (s t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
        x S' = mp F ψ (x S)) := by sorry
