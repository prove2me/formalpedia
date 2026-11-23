-- Prove2me | Theorems.Thm_GlobalTheory_LocDerExt_sep
-- name    : GlobalTheory.LocDerExt.sep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:55.861808+00:00
-- url     : https://prove2.me/theorems/38b85a71-659d-475e-bd5b-72c09abc1901
-- title:
--   Loc Der Ext: sep
-- statement:
--   The Loc Der Ext construction uses the sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationExtensionOfAffine.lean#L91-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationExtensionOfAffine.lean#L91-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.LocDerExt

theorem GlobalTheory.LocDerExt.sep {Y X : Scheme.{0}} (m : Y ⟶ X) {W₀ : X.Opens} (hW : IsAffineOpen W₀) {W : X.Opens}
    (h : W ≤ W₀) (s t : Γ(Y, m ⁻¹ᵁ W))
    (e : ∀ (f : Γ(X, W₀)) (k : X.basicOpen f ≤ W), resG Y (pre_le m k) s = resG Y (pre_le m k) t) :
    s = t := by sorry
