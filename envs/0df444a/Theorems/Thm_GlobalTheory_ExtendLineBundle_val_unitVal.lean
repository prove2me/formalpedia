-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_val_unitVal
-- name    : GlobalTheory.ExtendLineBundle.val_unitVal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:33.954095+00:00
-- url     : https://prove2.me/theorems/45a0266e-6d3f-4135-9247-8993f0f3b181
-- title:
--   Extend Line Bundle: val unit Val
-- statement:
--   The Extend Line Bundle construction uses the val unit Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L240-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L240-L243

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

theorem GlobalTheory.ExtendLineBundle.val_unitVal {U : X.Opens} (h : genericPoint X ∈ U) (a : Γ(X, U)ˣ) :
    (unitVal U a).val = X.presheaf.germ U _ h a.val := by sorry
