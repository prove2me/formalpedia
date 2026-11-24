-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_coinvariantsKer_le
-- name    : GroundTheory.Automorphic.map_coinvariantsKer_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:02.242343+00:00
-- url     : https://prove2.me/theorems/da2cda7e-0ace-4a3a-8056-51bd9f9b22b4
-- title:
--   Automorphic: map coinvariants Ker le
-- statement:
--   The Automorphic construction uses the map coinvariants Ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L58-L66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)

theorem GroundTheory.Automorphic.map_coinvariantsKer_le {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G) :
    coinvariantsKer ρ H ≤ (coinvariantsKer σ H).comap f.toLinearMap := by sorry
