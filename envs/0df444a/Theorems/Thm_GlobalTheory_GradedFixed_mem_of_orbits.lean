-- Prove2me | Theorems.Thm_GlobalTheory_GradedFixed_mem_of_orbits
-- name    : GlobalTheory.GradedFixed.mem_of_orbits
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:57:05.663809+00:00
-- url     : https://prove2.me/theorems/69326e1f-e94e-4395-a3ae-65fdfbe8bcc8
-- title:
--   Graded Fixed: mem of orbits
-- statement:
--   The Graded Fixed construction uses the mem of orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L167-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L167-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.GradedFixed.mem_of_orbits (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) (S : Submodule ℂ M) (F : Finset ι) :
    (∀ i ∈ F, ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
    ∀ u, (∀ g, π g u = u) → u ∈ WA V (⋃ i ∈ F, orbit G i) → u ∈ S := by sorry
