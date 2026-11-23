-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_coboundary_of_restrict
-- name    : GlobalTheory.CatCoh.Desc.coboundary_of_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:36.777835+00:00
-- url     : https://prove2.me/theorems/c2533137-3aa3-42a4-93d3-8eee076a3597
-- title:
--   Desc: coboundary of restrict
-- statement:
--   The Desc construction uses the coboundary of restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L39-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L39-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
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
open CategoryTheory Filter
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
universe v u w
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CatCoh.Desc.coboundary_of_restrict {E : C → Type w} (act : ∀ {S S'}, E S → (S ⟶ S') → E S')
    (hact : ∀ {S S' S''} (e : E S) (ψ : S ⟶ S') (χ : S' ⟶ S''), act e (ψ ≫ χ) = act (act e ψ) χ)
    (Q P : ∀ S, E S → Prop) (hQ : ∀ S S' e (ψ : S ⟶ S'), Q S e → Q S' (act e ψ))
    (sep : ∀ S e, Q S e → Sep F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (glue : ∀ S e, Q S e → Glue F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (van : ∀ S e, Q S e → Van1 F fun S' (ψ : S ⟶ S') ↦ P S' (act e ψ))
    (z : ∀ S S' S'', E S → (S ⟶ S') → (S' ⟶ S'') → F.obj S'')
    (hz : ∀ S S' S'' S''' e ψ χ ω, Q S e → mp F ω (z S S' S'' e ψ χ) + z S S'' S''' e (ψ ≫ χ) ω =
      z S S' S''' e ψ (χ ≫ ω) + z S' S'' S''' (act e ψ) χ ω)
    (f : ∀ S S', E S → (S ⟶ S') → F.obj S')
    (hf : ∀ S S' S'' e ψ χ, P S e →
      mp F χ (f S S' e ψ) - f S S'' e (ψ ≫ χ) + f S' S'' (act e ψ) χ = z S S' S'' e ψ χ) :
    ∃ h : ∀ S S', E S → (S ⟶ S') → F.obj S', ∀ S S' S'' e ψ χ, Q S e →
      mp F χ (h S S' e ψ) - h S S'' e (ψ ≫ χ) + h S' S'' (act e ψ) χ = z S S' S'' e ψ χ := by sorry
