-- Prove2me | Theorems.Thm_GlobalTheory_NormGlue_exists_ext
-- name    : GlobalTheory.NormGlue.exists_ext
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:01.618387+00:00
-- url     : https://prove2.me/theorems/1c056b36-71c0-5c22-87e9-439169614bd7
-- title:
--   Norm Glue: exists ext
-- statement:
--   The Norm Glue construction uses the exists ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L111-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L111-L144

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

theorem GlobalTheory.NormGlue.exists_ext (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π]
    [LocallyOfFiniteType π] (hX : Geo.Tor.IsNormalScheme X) {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (W : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ W) (hne : (W : Set X).Nonempty → (V : Set Y).Nonempty)
    (u : Γ(Y, V)ˣ)
    (hu : ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ Y), IntAt f W x → Set.range x ⊆ V →
      ‖valF x V u.val‖ = 1) :
    ∃ ψ : Γ(X, W)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ V → gm (r ≫ f) z W ψ = gm r z V u := by sorry
