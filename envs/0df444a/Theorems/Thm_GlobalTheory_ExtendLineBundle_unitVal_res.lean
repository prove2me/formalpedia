-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_unitVal_res
-- name    : GlobalTheory.ExtendLineBundle.unitVal_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:05.577394+00:00
-- url     : https://prove2.me/theorems/c6346c46-1717-423b-87df-10e7579d1589
-- title:
--   Extend Line Bundle: unit Val res
-- statement:
--   The Extend Line Bundle construction uses the unit Val res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L245-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L245-L249

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

theorem GlobalTheory.ExtendLineBundle.unitVal_res {U V : X.Opens} (hle : V ≤ U) (h : genericPoint X ∈ V) (a : Γ(X, U)ˣ) :
    unitVal V (res hle a) = unitVal U a := by sorry
