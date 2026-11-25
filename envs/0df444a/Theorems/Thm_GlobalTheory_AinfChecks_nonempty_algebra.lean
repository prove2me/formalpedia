-- Prove2me | Theorems.Thm_GlobalTheory_AinfChecks_nonempty_algebra
-- name    : GlobalTheory.AinfChecks.nonempty_algebra
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:32.348543+00:00
-- url     : https://prove2.me/theorems/06a0fb96-9b3a-57ed-bee5-22f63401bc33
-- title:
--   Ainf Checks: nonempty algebra
-- statement:
--   The Ainf Checks construction uses the nonempty algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/NonemptyAlgebra.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/NonemptyAlgebra.lean#L36-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WittVector Ideal ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.AinfChecks
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
omit [IsAdicComplete (span {(p : O)}) O]

theorem GlobalTheory.AinfChecks.nonempty_algebra (pflat : PreTilt O p) :
    Nonempty (Algebra (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
      span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})) := by sorry
