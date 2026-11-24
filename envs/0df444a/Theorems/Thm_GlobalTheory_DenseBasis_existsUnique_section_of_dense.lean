-- Prove2me | Theorems.Thm_GlobalTheory_DenseBasis_existsUnique_section_of_dense
-- name    : GlobalTheory.DenseBasis.existsUnique_section_of_dense
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:41.755904+00:00
-- url     : https://prove2.me/theorems/4566c53a-b2fa-42ef-9f7a-9763fd770cf7
-- title:
--   Dense Basis: exists Unique section of dense
-- statement:
--   The Dense Basis construction uses the exists Unique section of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueSectionOfDense.lean#L54-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueSectionOfDense.lean#L54-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteEtaleLatticeTorsionHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.DenseBasis
variable {Z S : Scheme.{0}}

theorem GlobalTheory.DenseBasis.existsUnique_section_of_dense (p : Z ⟶ S) [IsFinite p] [Etale p] {I : Type} [Finite I]
    (σ : I → (S ⟶ Z)) (hσ : ∀ i, σ i ≫ p = 𝟙 S) (D : Set S) (hD : Dense D)
    (h : ∀ t ∈ D, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Spec (.of K) ⟶ S),
      t ∈ Set.range x ∧ ∀ y : Spec (.of K) ⟶ Z, y ≫ p = x → ∃! i, x ≫ σ i = y)
    (K : Type) [Field K] (x : Spec (.of K) ⟶ S) (y : Spec (.of K) ⟶ Z) (hy : y ≫ p = x) :
    ∃! i, x ≫ σ i = y := by sorry
