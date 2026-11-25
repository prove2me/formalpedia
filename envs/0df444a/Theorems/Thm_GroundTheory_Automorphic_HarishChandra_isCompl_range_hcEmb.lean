-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_isCompl_range_hcEmb
-- name    : GroundTheory.Automorphic.HarishChandra.isCompl_range_hcEmb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:19.084453+00:00
-- url     : https://prove2.me/theorems/4d614677-6792-4ecd-9d44-d0c117bd1a66
-- title:
--   Harish Chandra: is Compl range hc Emb
-- statement:
--   The Harish Chandra construction uses the is Compl range hc Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L120-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L120-L131

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
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

theorem GroundTheory.Automorphic.HarishChandra.isCompl_range_hcEmb :
    IsCompl (LinearMap.range (hcEmb (n := n)).toLinearMap) (nMinusU n ⊔ nPlusU n) := by sorry
