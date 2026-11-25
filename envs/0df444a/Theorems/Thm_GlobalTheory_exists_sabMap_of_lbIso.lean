-- Prove2me | Theorems.Thm_GlobalTheory_exists_sabMap_of_lbIso
-- name    : GlobalTheory.exists_sabMap_of_lbIso
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:36.154557+00:00
-- url     : https://prove2.me/theorems/e4a87387-8312-4b3e-8a03-a74b723e2040
-- title:
--   Global Theory: exists sab Map of lb Iso
-- statement:
--   The Global Theory construction uses the exists sab Map of lb Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSabMapOfLbIso.lean#L94-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSabMapOfLbIso.lean#L94-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGeometricallyIntegralAbLocusTensorObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfLbIso
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.exists_sabMap_of_lbIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (φ : t'.G.left ⟶ t.G.left), (IsReduced X' ∧ genericPoints X' ⊆ abLocus t'.G) → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ ν : SABMap t' t f, ν.φ = φ := by sorry
