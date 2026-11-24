-- Prove2me | Theorems.Thm_GlobalTheory_OrbitAvg_avg_pair
-- name    : GlobalTheory.OrbitAvg.avg_pair
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:37:40.086512+00:00
-- url     : https://prove2.me/theorems/d141f545-8dfc-4635-bae9-228bae433e8e
-- title:
--   Orbit Avg: avg pair
-- statement:
--   The Orbit Avg construction uses the avg pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L174-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L174-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)

theorem GlobalTheory.OrbitAvg.avg_pair {x y : V} (hx : (stab π L x).FiniteIndex) (hy : (stab π L y).FiniteIndex) :
    ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
      avg π L x = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g x ∧
      avg π L y = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g y ∧
      Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ y = π (f g) y := by sorry
