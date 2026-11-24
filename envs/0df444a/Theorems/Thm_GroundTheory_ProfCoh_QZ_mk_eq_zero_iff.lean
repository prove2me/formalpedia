-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZ_mk_eq_zero_iff
-- name    : GroundTheory.ProfCoh.QZ.mk_eq_zero_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:24.345229+00:00
-- url     : https://prove2.me/theorems/02bb6350-de19-45bd-b59e-b4c7c7c3168d
-- title:
--   QZ: mk eq zero iff
-- statement:
--   The QZ construction uses the mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L34-L35

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
open GroundTheory.ProfCoh.QZ

theorem GroundTheory.ProfCoh.QZ.mk_eq_zero_iff (q : ℚ) : mk q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by sorry
