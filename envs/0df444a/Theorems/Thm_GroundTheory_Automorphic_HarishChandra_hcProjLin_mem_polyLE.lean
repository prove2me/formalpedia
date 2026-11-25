-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcProjLin_mem_polyLE
-- name    : GroundTheory.Automorphic.HarishChandra.hcProjLin_mem_polyLE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:55:27.145745+00:00
-- url     : https://prove2.me/theorems/134c0b66-ef03-45cb-a76a-b88ae94c79eb
-- title:
--   Harish Chandra: hc Proj Lin mem poly LE
-- statement:
--   The Harish Chandra construction uses the hc Proj Lin mem poly LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L36-L46

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

theorem GroundTheory.Automorphic.HarishChandra.hcProjLin_mem_polyLE {d : ℕ} {u : U n} (hu : u ∈ filt d) : hcProjLin u ∈ polyLE n d := by sorry
