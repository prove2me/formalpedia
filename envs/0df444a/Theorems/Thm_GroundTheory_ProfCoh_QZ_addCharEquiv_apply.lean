-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZ_addCharEquiv_apply
-- name    : GroundTheory.ProfCoh.QZ.addCharEquiv_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:17:12.478774+00:00
-- url     : https://prove2.me/theorems/7eb34b1a-8616-53f3-9d13-630b12fa4c43
-- title:
--   QZ: add Char Equiv apply
-- statement:
--   The QZ construction uses the add Char Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L140-L142

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
open GroundTheory.ProfCoh.QZ
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem GroundTheory.ProfCoh.QZ.addCharEquiv_apply [Finite G] (f : G →+ QZ) (a : G) :
    addCharEquiv G f a = toComplex (f a) := by sorry

attribute [defeq] GroundTheory.ProfCoh.QZ.addCharEquiv_apply
