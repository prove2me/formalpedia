-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_lineBundle_height_properScheme
-- name    : GlobalTheory.T.exists_lineBundle_height_properScheme
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:36:59.600438+00:00
-- url     : https://prove2.me/theorems/43140469-5bb7-425b-a22a-8e399d2bfba0
-- title:
--   T: exists line Bundle height proper Scheme
-- statement:
--   The T construction uses the exists line Bundle height proper Scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperSchemeStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleHeightProperSchemeStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperSchemeStatement
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
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_lineBundle_height_properScheme : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (Pl : Places k K) (B : Over (Sp k)), IsProper B.hom → ∀ (L : LB B.left), L.IsLB → ∃ h : (Over.mk (spMap (algebraMap k K)) ⟶ B) → ℤ, (∀ (Z : Over (Sp k)), IsProper Z.hom → ∀ (n : ℕ) (φ : Fin n → (Z ⟶ B)) (ε : Fin n → ℤ), (∃ t : LB.Gen (LB.LinComb L (fun i => (φ i).left) ε), t.IsGen) → ∀ z : Over.mk (spMap (algebraMap k K)) ⟶ Z, ∑ i, ε i * h (z ≫ φ i) = 0) ∧ ∀ (N : ℕ) (s : LB.Sec (GlobalTheory.AbLaw.pw L N)) (x : Over.mk (spMap (algebraMap k K)) ⟶ B), 1 ≤ N → Set.range x.left ⊆ Out.nonzeroLocus s → 0 ≤ h x ∧ (h x = 0 → ∀ i, ∃ b : Sp (Pl.O i) ⟶ B.left, spMap (Pl.O i).subtype ≫ b = x.left ∧ Set.range b ⊆ Out.nonzeroLocus s) := by sorry
