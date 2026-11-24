-- Prove2me | Theorems.Thm_GlobalTheory_ZV_TorsBasis_existsUnique
-- name    : GlobalTheory.ZV.TorsBasis.existsUnique
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:49.758018+00:00
-- url     : https://prove2.me/theorems/b5462dd5-0f71-450d-9c95-beb3c8325ee0
-- title:
--   Tors Basis: exists Unique
-- statement:
--   The Tors Basis construction uses the exists Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/SectionsHaveFiniteDimension.lean#L187-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/SectionsHaveFiniteDimension.lean#L187-L188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
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
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
variable {A : Over (Sp K)} [GrpObj A] {k m : ℕ} {pt : Fin m → (Out.baseOver (Sp K) ⟶ A)}

theorem GlobalTheory.ZV.TorsBasis.existsUnique (h : TorsBasis A k pt) {y : Out.baseOver (Sp K) ⟶ A} (hy : y ^ k = 1) :
    ∃! c : Fin m → ZMod k, Out.linComb pt (fun i => (c i).val) = y := by sorry
