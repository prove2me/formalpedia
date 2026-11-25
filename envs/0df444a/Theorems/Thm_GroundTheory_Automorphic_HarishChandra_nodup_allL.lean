-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nodup_allL
-- name    : GroundTheory.Automorphic.HarishChandra.nodup_allL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:08:02.574218+00:00
-- url     : https://prove2.me/theorems/4a7da1cc-c948-4629-bd4d-78088cef77a6
-- title:
--   Harish Chandra: nodup all L
-- statement:
--   The Harish Chandra construction uses the nodup all L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L40-L49

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
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

theorem GroundTheory.Automorphic.HarishChandra.nodup_allL : (allL n).Nodup := by sorry
