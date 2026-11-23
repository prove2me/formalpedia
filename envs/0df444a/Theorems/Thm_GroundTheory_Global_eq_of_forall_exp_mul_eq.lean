-- Prove2me | Theorems.Thm_GroundTheory_Global_eq_of_forall_exp_mul_eq
-- name    : GroundTheory.Global.eq_of_forall_exp_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:30.454792+00:00
-- url     : https://prove2.me/theorems/29fca371-1135-4946-b5ec-3a038fab1dc1
-- title:
--   Global: eq of forall exp mul eq
-- statement:
--   The Global construction uses the eq of forall exp mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchChars.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ArchChars.lean#L42-L50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex

theorem GroundTheory.Global.eq_of_forall_exp_mul_eq {s s' : ℂ}
    (h : ∀ t : ℝ, Complex.exp (s * t) = Complex.exp (s' * t)) : s = s' := by sorry
