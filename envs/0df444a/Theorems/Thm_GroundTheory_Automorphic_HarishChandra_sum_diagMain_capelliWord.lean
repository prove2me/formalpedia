-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_diagMain_capelliWord
-- name    : GroundTheory.Automorphic.HarishChandra.sum_diagMain_capelliWord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:25.782339+00:00
-- url     : https://prove2.me/theorems/b44d4fb5-f013-42d5-b328-2af4de726fda
-- title:
--   Harish Chandra: sum diag Main capelli Word
-- statement:
--   The Harish Chandra construction uses the sum diag Main capelli Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L148-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L148-L156

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

theorem GroundTheory.Automorphic.HarishChandra.sum_diagMain_capelliWord (k : ℕ) :
    ∑ i : Fin (k + 1) → Fin n,
      diagMain (List.ofFn fun t : Fin (k + 1) => (i t, i (finRotate (k + 1) t))) =
        psum (Fin n) ℂ (k + 1) := by sorry
