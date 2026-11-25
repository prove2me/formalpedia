-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_translate_sub_mem_polyLE
-- name    : GroundTheory.Automorphic.HarishChandra.translate_sub_mem_polyLE
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:29.784321+00:00
-- url     : https://prove2.me/theorems/be26cbfe-7c22-4326-b64b-789d76d4e27f
-- title:
--   Harish Chandra: translate sub mem poly LE
-- statement:
--   The Harish Chandra construction uses the translate sub mem poly LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L185-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L185-L242

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

theorem GroundTheory.Automorphic.HarishChandra.translate_sub_mem_polyLE (c : Fin n → ℂ) :
    ∀ (d : ℕ) (p : MvPolynomial (Fin n) ℂ), p ∈ polyLE n d → translate c p - p ∈ polyLE n (d - 1) := by sorry
