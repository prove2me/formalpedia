-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZDual_eval_apply
-- name    : GroundTheory.ProfCoh.QZDual.eval_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:19.380486+00:00
-- url     : https://prove2.me/theorems/6d43475b-b97e-4fc7-972f-f96ca7ee5d34
-- title:
--   QZDual: eval apply
-- statement:
--   The QZDual construction uses the eval apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L90-L91

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
open GroundTheory.ProfCoh.QZDual
variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]

theorem GroundTheory.ProfCoh.QZDual.eval_apply (a : A) (χ : QZDual A) : eval A a χ = χ a := by sorry

attribute [defeq] GroundTheory.ProfCoh.QZDual.eval_apply
