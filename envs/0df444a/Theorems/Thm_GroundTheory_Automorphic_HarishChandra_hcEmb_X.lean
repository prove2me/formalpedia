-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
-- name    : GroundTheory.Automorphic.HarishChandra.hcEmb_X
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:49.58706+00:00
-- url     : https://prove2.me/theorems/1c4b57d6-b334-42f6-bc09-9f62beb4384a
-- title:
--   Harish Chandra: hc Emb X
-- statement:
--   The Harish Chandra construction uses the hc Emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L143-L144

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
open scoped IsMulCommutative

theorem GroundTheory.Automorphic.HarishChandra.hcEmb_X (i : Fin n) : hcEmb (X i) = e (n := n) (i, i) := by sorry
