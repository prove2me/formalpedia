-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_single
-- name    : GroundTheory.Automorphic.HarishChandra.diagExp_single
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:49.691184+00:00
-- url     : https://prove2.me/theorems/95e0461f-f2b8-5a14-a953-a9180ca6edfe
-- title:
--   Harish Chandra: diag Exp single
-- statement:
--   The Harish Chandra construction uses the diag Exp single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L59-L64

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

theorem GroundTheory.Automorphic.HarishChandra.diagExp_single (i : Fin n) : diagExp (Finsupp.single (i, i) 1) = Finsupp.single i 1 := by sorry
