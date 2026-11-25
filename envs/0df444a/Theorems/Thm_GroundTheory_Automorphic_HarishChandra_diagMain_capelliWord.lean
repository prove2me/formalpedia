-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagMain_capelliWord
-- name    : GroundTheory.Automorphic.HarishChandra.diagMain_capelliWord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:03:05.582935+00:00
-- url     : https://prove2.me/theorems/99dcf0a4-7daf-467d-8509-e51901c74f27
-- title:
--   Harish Chandra: diag Main capelli Word
-- statement:
--   The Harish Chandra construction uses the diag Main capelli Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L118-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L118-L146

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.diagMain_capelliWord {k : ℕ} (i : Fin (k + 1) → Fin n) :
    diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
      ∑ c : Fin n, if i = (fun _ => c) then X c ^ (k + 1) else 0 := by sorry
