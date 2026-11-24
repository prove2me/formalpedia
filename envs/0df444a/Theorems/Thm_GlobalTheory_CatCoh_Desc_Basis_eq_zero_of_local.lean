-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local
-- name    : GlobalTheory.CatCoh.Desc.Basis.eq_zero_of_local
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:13:49.345412+00:00
-- url     : https://prove2.me/theorems/2b699a13-8cb9-4816-8b70-3b6a65e5f474
-- title:
--   Basis: eq zero of local
-- statement:
--   The Basis construction uses the eq zero of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCocycleCoboundaryCommaLocalBasis.lean#L21-L33

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

theorem GlobalTheory.CatCoh.Desc.Basis.eq_zero_of_local (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by sorry
