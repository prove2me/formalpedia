-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_injective
-- name    : GroundTheory.Automorphic.HarishChandra.hcEmb_injective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:11.4198+00:00
-- url     : https://prove2.me/theorems/2a08658f-5de6-48d8-9ab1-a4a7962a5fdb
-- title:
--   Harish Chandra: hc Emb injective
-- statement:
--   The Harish Chandra construction uses the hc Emb injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Projection.lean#L63-L64

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

theorem GroundTheory.Automorphic.HarishChandra.hcEmb_injective : Function.Injective (hcEmb (n := n)) := by sorry
