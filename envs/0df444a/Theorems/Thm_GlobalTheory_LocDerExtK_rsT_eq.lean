-- Prove2me | Theorems.Thm_GlobalTheory_LocDerExtK_rsT_eq
-- name    : GlobalTheory.LocDerExtK.rsT_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:37:50.649114+00:00
-- url     : https://prove2.me/theorems/4b0f01ab-7066-4d0a-b15b-8f12a6c6dd11
-- title:
--   Loc Der Ext K: rs T eq
-- statement:
--   The Loc Der Ext K construction uses the rs T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueLocalDerivationAlongFibreFieldOfAffi.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueLocalDerivationAlongFibreFieldOfAffi.lean#L16-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
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
open GlobalTheory GlobalTheory.LocDerExtK
open GlobalTheory.LocDerExt

theorem GlobalTheory.LocDerExtK.rsT_eq {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    rsT s O = resG Y h s := by sorry
