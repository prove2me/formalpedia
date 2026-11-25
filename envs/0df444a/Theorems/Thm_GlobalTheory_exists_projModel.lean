-- Prove2me | Theorems.Thm_GlobalTheory_exists_projModel
-- name    : GlobalTheory.exists_projModel
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:32:37.803215+00:00
-- url     : https://prove2.me/theorems/5800bd0a-ee70-4c65-bd16-f63d637fc03a
-- title:
--   Global Theory: exists proj Model
-- statement:
--   The Global Theory construction uses the exists proj Model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L319-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean#L319-L362

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory
open ProjCone
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.exists_projModel {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) (hP : I.IsPrime) (hX : ∃ c, X c ∉ I) (g : ℕ)
    (hg : ringKrullDim (MvPolynomial σ ℂ ⧸ I) ≤ (g + 1 : ℕ)) :
    ∃ (Y : Over (Sp ℂ)) (D : σ → Y.left.Opens) (r : ∀ c, σ → Γ(Y.left, D c)),
      IsIntegral Y.left ∧ IsProper Y.hom ∧ (⨆ c, D c = ⊤) ∧ (∀ c, IsAffineOpen (D c)) ∧
      (∀ c, ringKrullDim Γ(Y.left, D c) ≤ g) ∧
      (∀ c (f : Γ(Y.left, D c)), ∃ F : MvPolynomial σ ℂ, f = eval₂ (RingHom.comp (Y.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r c) F) ∧
      (∀ c, ∀ F ∈ I, eval₂ (RingHom.comp (Y.hom.appLE ⊤ (D c) le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) (r c) F = 0) ∧
      (∀ c, r c c = 1) ∧
      (∀ c (p : σ → ℂ), (∀ F ∈ I, eval p F = 0) → p c ≠ 0 → ∃ e : Γ(Y.left, D c) →+* ℂ,
        (∀ a, e (constFn Y.hom (D c) a) = a) ∧ ∀ c', e (r c c') = p c' / p c) ∧
      (∀ c c', Y.left.basicOpen (r c c') ≤ D c') ∧
      (∀ c c' q, resG _ (inf_le_left : D c ⊓ D c' ≤ _) (r c q) * resG _ (inf_le_right : D c ⊓ D c' ≤ _) (r c' c) =
        resG _ (inf_le_right : D c ⊓ D c' ≤ _) (r c' q)) := by sorry
