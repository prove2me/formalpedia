-- Prove2me | Theorems.Thm_GlobalTheory_exists_lineBundle_of_normOne_generators
-- name    : GlobalTheory.exists_lineBundle_of_normOne_generators
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:15:41.900851+00:00
-- url     : https://prove2.me/theorems/aaa9ec00-50b1-4913-9b4e-ef22d61887a8
-- title:
--   Global Theory: exists line Bundle of norm One generators
-- statement:
--   The Global Theory construction uses the exists line Bundle of norm One generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L225-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L225-L300

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
open NormGlue

theorem GlobalTheory.exists_lineBundle_of_normOne_generators : ∀ (X A₀ : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π], Geo.Tor.IsNormalScheme X → ∀ (a : A₀ ⟶ X) [IsOpenImmersion a] (L : LB A₀), L.IsLB → ∀ ν : Nrm L, IsNrm L ν → (∀ w : X, IsClosed ({w} : Set X) → ∃ (W : X.Opens) (W₀ : A₀.Opens) (gen₀ : LB.Gen (L.pull W₀.ι)), w ∈ W ∧ (W₀ : Set A₀).Nonempty ∧ gen₀.IsGen ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ W₀.toScheme), IntAt (W₀.ι ≫ a) W x → NormOne ν gen₀ x) → ∃ (M : LB X) (w : LB.Iso (M.pull a) L) (D : M.ι → A₀.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set A₀).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ A₀) (i : M.ι) (j : L.ι), IntAt a (M.U i) x → Set.range x ⊆ L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1 := by sorry
