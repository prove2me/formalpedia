-- Prove2me | Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_section_of_mem
-- name    : GlobalTheory.ExtendLineBundle.exists_section_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:24.193972+00:00
-- url     : https://prove2.me/theorems/bc714515-34f7-4222-a0b8-d446716f11ac
-- title:
--   Extend Line Bundle: exists section of mem
-- statement:
--   The Extend Line Bundle construction uses the exists section of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLineBundleExtension.lean#L30-L35

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

theorem GlobalTheory.ExtendLineBundle.exists_section_of_mem {x : X} {t : X.functionField} (ht : t ∈ localSubring x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      X.presheaf.germ U _ (genericPoint_mem hx) s = t := by sorry
