-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZDual_addCharEquiv_apply
-- name    : GroundTheory.ProfCoh.QZDual.addCharEquiv_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:34.848285+00:00
-- url     : https://prove2.me/theorems/dfabc294-65ca-4872-8c9c-11a6bf3c4dac
-- title:
--   QZDual: add Char Equiv apply
-- statement:
--   The QZDual construction uses the add Char Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L154-L156

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
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
open Function
open GroundTheory.ProfCoh.QZDual
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]

theorem GroundTheory.ProfCoh.QZDual.addCharEquiv_apply [Finite N] (χ : QZDual N) (a : N) :
    addCharEquiv χ a = QZ.toComplex (χ a) := by sorry

attribute [defeq] GroundTheory.ProfCoh.QZDual.addCharEquiv_apply
