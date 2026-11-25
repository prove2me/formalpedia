-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZ_finite_setOf_nsmul_eq_zero
-- name    : GroundTheory.ProfCoh.QZ.finite_setOf_nsmul_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:55.734582+00:00
-- url     : https://prove2.me/theorems/2748cf0c-7f3c-4e22-a612-33a03190c212
-- title:
--   QZ: finite set Of nsmul eq zero
-- statement:
--   The QZ construction uses the finite set Of nsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualFinite.lean#L11-L12

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

theorem GroundTheory.ProfCoh.QZ.finite_setOf_nsmul_eq_zero {n : ℕ} (hn : 0 < n) : {x : QZ | n • x = 0}.Finite := by sorry
