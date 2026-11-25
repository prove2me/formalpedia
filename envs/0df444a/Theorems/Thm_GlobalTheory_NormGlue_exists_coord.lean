-- Prove2me | Theorems.Thm_GlobalTheory_NormGlue_exists_coord
-- name    : GlobalTheory.NormGlue.exists_coord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:15:52.731951+00:00
-- url     : https://prove2.me/theorems/0e15560d-845b-4b09-a3d0-b2abe99f5da6
-- title:
--   Norm Glue: exists coord
-- statement:
--   The Norm Glue construction uses the exists coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L146-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L146-L220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
open GlobalTheory.NormGlue

theorem GlobalTheory.NormGlue.exists_coord (X A₀ : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π]
    (hX : Geo.Tor.IsNormalScheme X) (a : A₀ ⟶ X) [IsOpenImmersion a] (L : LB A₀) (ν : Nrm L) (hν : IsNrm L ν)
    (W : X.Opens) (W₀ : A₀.Opens) (gn : LB.Gen (L.pull W₀.ι)) (hW₀ : (W₀ : Set A₀).Nonempty) (hgen : gn.IsGen)
    (hn : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ W₀.toScheme), IntAt (W₀.ι ≫ a) W x → NormOne ν gn x) :
    ∃ s : ∀ j, Γ(A₀, L.U j ⊓ a ⁻¹ᵁ W)ˣ,
      (∀ (y : A₀) (j j' : L.ι), y ∈ L.U j → y ∈ L.U j' → a y ∈ W →
        gm (𝟙 A₀) y _ (s j) = gm (𝟙 A₀) y _ (L.g j j') * gm (𝟙 A₀) y _ (s j')) ∧
      ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ A₀) (j : L.ι), IntAt a W x → Set.range x ⊆ L.U j →
        Set.range x ⊆ W₀ → ‖valF x _ (s j).val‖ * ν p x j = 1 := by sorry
