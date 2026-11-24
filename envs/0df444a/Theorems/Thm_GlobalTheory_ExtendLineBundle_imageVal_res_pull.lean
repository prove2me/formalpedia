-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_imageVal_res_pull
-- name    : GlobalTheory.ExtendLineBundle.imageVal_res_pull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:34.530574+00:00
-- url     : https://prove2.me/theorems/216e8762-2ca7-4162-97ac-3dd449f35bee
-- title:
--   Extend Line Bundle: image Val res pull
-- statement:
--   The Extend Line Bundle construction uses the image Val res pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L299-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L299-L303

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
variable (j : Y ⟶ X) [IsOpenImmersion j]

theorem GlobalTheory.ExtendLineBundle.imageVal_res_pull {U : X.Opens} {V : Y.Opens} (hle : V ≤ j ⁻¹ᵁ U)
    (h : genericPoint X ∈ j ''ᵁ V) (a : Γ(X, U)ˣ) :
    imageVal j V (res hle (pullU j U a)) = unitVal U a := by sorry
