-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_unitVal_mem
-- name    : GlobalTheory.ExtendLineBundle.unitVal_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:37.142324+00:00
-- url     : https://prove2.me/theorems/609ec4e5-77ca-4a5d-baab-7620285ce926
-- title:
--   Extend Line Bundle: unit Val mem
-- statement:
--   The Extend Line Bundle construction uses the unit Val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L261-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L261-L265

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]

theorem GlobalTheory.ExtendLineBundle.unitVal_mem {U : X.Opens} {y : X} (hy : y ∈ U) (a : Γ(X, U)ˣ) :
    unitVal U a ∈ localUnits y := by sorry
