-- Prove2me | Theorems.Thm_GlobalTheory_PerfectCompletion_pow_root
-- name    : GlobalTheory.PerfectCompletion.pow_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:05.518853+00:00
-- url     : https://prove2.me/theorems/b9288b92-e464-42ae-80af-3598f079f662
-- title:
--   Perfect Completion: pow root
-- statement:
--   The Perfect Completion construction uses the pow root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdicCompletionPrincipalPerfect.lean#L58-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable (l : ℕ) [Fact l.Prime] {V : Type} [CommRing V] [CharP V l] [PerfectRing V l]

theorem GlobalTheory.PerfectCompletion.pow_root (c : V) : ((frobeniusEquiv V l).symm c) ^ l = c := by sorry
