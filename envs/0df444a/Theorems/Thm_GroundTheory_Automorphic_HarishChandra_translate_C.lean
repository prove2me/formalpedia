-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_C
-- name    : GroundTheory.Automorphic.HarishChandra.translate_C
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:23.858342+00:00
-- url     : https://prove2.me/theorems/5c17141a-4a05-4544-a4d8-84125a14cedc
-- title:
--   Harish Chandra: translate C
-- statement:
--   The Harish Chandra construction uses the translate C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L172-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L172-L173

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

theorem GroundTheory.Automorphic.HarishChandra.translate_C (c : Fin n → ℂ) (a : ℂ) : translate c (C a) = C a := by sorry
