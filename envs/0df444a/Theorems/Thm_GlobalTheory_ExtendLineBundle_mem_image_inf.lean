-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_mem_image_inf
-- name    : GlobalTheory.ExtendLineBundle.mem_image_inf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:51.280697+00:00
-- url     : https://prove2.me/theorems/c6c4827e-28a6-4034-999f-9b7d351d3b30
-- title:
--   Extend Line Bundle: mem image inf
-- statement:
--   The Extend Line Bundle construction uses the mem image inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L320-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L320-L323

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
omit [IsIntegral X]

theorem GlobalTheory.ExtendLineBundle.mem_image_inf {U V : Y.Opens} {x : X} (hU : x ∈ j ''ᵁ U) (hV : x ∈ j ''ᵁ V) :
    x ∈ j ''ᵁ (U ⊓ V) := by sorry
