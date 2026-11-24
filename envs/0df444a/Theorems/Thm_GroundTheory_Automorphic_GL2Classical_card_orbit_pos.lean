-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_card_orbit_pos
-- name    : GroundTheory.Automorphic.GL2Classical.card_orbit_pos
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:25.566597+00:00
-- url     : https://prove2.me/theorems/7f110f0b-2fe7-4fdc-8a4e-6c2aec803a53
-- title:
--   GL2 Classical: card orbit pos
-- statement:
--   The GL2 Classical construction uses the card orbit pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/UnitaryEigenSpan.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/UnitaryEigenSpan.lean#L50-L52

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_UnitaryEigenSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)
variable {ρ}

theorem GroundTheory.Automorphic.GL2Classical.card_orbit_pos {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite) :
    0 < hv.toFinset.card := by sorry
