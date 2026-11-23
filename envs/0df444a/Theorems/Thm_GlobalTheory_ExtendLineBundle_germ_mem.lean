-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_germ_mem
-- name    : GlobalTheory.ExtendLineBundle.germ_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:27.267698+00:00
-- url     : https://prove2.me/theorems/20f1764e-b6ad-4a5d-a2d4-03280be2a90d
-- title:
--   Extend Line Bundle: germ mem
-- statement:
--   The Extend Line Bundle construction uses the germ mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L26-L28

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

theorem GlobalTheory.ExtendLineBundle.germ_mem {U : X.Opens} {x : X} (hx : x ∈ U) (h : genericPoint X ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U _ h s ∈ localSubring x := by sorry
