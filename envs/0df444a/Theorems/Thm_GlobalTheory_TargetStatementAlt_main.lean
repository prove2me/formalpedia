-- Prove2me | Theorems.Thm_GlobalTheory_TargetStatementAlt_main
-- name    : GlobalTheory.TargetStatementAlt.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:51.130219+00:00
-- url     : https://prove2.me/theorems/40d09015-d162-4167-a873-f0880dd0b269
-- title:
--   Target Statement Alt: main
-- statement:
--   The Target Statement Alt construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsAlt.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsAlt.lean#L7-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TargetStatementAlt
open Polynomial

theorem GlobalTheory.TargetStatementAlt.main {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) :
    IsIntegral R (Matrix.trace M) := by sorry
