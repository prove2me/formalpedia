-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_X
-- name    : GroundTheory.Automorphic.HarishChandra.translate_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:18.559172+00:00
-- url     : https://prove2.me/theorems/cd962e21-57cc-5f09-ac93-a105c17874ab
-- title:
--   Harish Chandra: translate X
-- statement:
--   The Harish Chandra construction uses the translate X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L169-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L169-L170

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

theorem GroundTheory.Automorphic.HarishChandra.translate_X (c : Fin n → ℂ) (i : Fin n) : translate c (X i) = X i + C (c i) := by sorry
