-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_polyLE_mono
-- name    : GroundTheory.Automorphic.HarishChandra.polyLE_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:54:11.315331+00:00
-- url     : https://prove2.me/theorems/0b00cdf2-b147-5fc4-ae76-3c40a1291c99
-- title:
--   Harish Chandra: poly LE mono
-- statement:
--   The Harish Chandra construction uses the poly LE mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L18-L19

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

theorem GroundTheory.Automorphic.HarishChandra.polyLE_mono {d d' : ℕ} (h : d ≤ d') : polyLE n d ≤ polyLE n d' := by sorry
