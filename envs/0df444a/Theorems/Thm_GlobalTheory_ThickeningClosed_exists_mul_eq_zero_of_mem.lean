-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningClosed_exists_mul_eq_zero_of_mem
-- name    : GlobalTheory.ThickeningClosed.exists_mul_eq_zero_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:47.836261+00:00
-- url     : https://prove2.me/theorems/80b8198c-0b63-40e3-b151-5c078eddb3e1
-- title:
--   Thickening Closed: exists mul eq zero of mem
-- statement:
--   The Thickening Closed construction uses the exists mul eq zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L57-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L57-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ThickeningClosed.exists_mul_eq_zero_of_mem {X : Scheme.{0}} (K : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U))
    (hq : U.2.fromSpec q ∈ _root_.GlobalTheory.ThickeningClosed.zeroLocusOpen K) {a : Γ(X, U)}
    (ha : a ∈ K.ideal U) : ∃ s ∉ q.asIdeal, s * a = 0 := by sorry
