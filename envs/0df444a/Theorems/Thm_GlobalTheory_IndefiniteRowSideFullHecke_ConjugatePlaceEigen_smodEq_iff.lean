-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_smodEq_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.smodEq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:30.316812+00:00
-- url     : https://prove2.me/theorems/e6c748e7-3913-482e-96a5-c020068a46ac
-- title:
--   Conjugate Place Eigen: smod Eq iff
-- statement:
--   The Conjugate Place Eigen construction uses the smod Eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ConjugatePlaceEigen.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ConjugatePlaceEigen.lean#L48-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out
open Ideal
variable (p : ℕ) [hp : Fact p.Prime]

theorem GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.smodEq_iff (n : ℕ) (x y : 𝓞_ℂ_[p]) :
    x ≡ y [SMOD ((span {((p : ℕ) : 𝓞_ℂ_[p])}) ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by sorry
