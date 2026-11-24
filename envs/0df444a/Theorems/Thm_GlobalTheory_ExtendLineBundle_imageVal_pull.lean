-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_imageVal_pull
-- name    : GlobalTheory.ExtendLineBundle.imageVal_pull
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:37.76999+00:00
-- url     : https://prove2.me/theorems/d3c68688-b719-46f5-9645-1ca54ccae4c6
-- title:
--   Extend Line Bundle: image Val pull
-- statement:
--   The Extend Line Bundle construction uses the image Val pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L361-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L361-L365

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

theorem GlobalTheory.ExtendLineBundle.imageVal_pull (M : LB X) (p q : PUnit → M.ι)
    (h : genericPoint X ∈ j ''ᵁ (LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q)) :
    imageVal j _ ((M.pull j).g p q) = unitVal _ (M.g (p ⟨⟩) (q ⟨⟩)) := by sorry
