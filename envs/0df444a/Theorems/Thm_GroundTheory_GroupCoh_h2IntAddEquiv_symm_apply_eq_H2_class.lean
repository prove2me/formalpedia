-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_h2IntAddEquiv_symm_apply_eq_H2_class
-- name    : GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply_eq_H2_class
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:59.755419+00:00
-- url     : https://prove2.me/theorems/b68f2ddc-3d3b-547f-a774-80985268233d
-- title:
--   Group Coh: h2 Int Add Equiv symm apply eq H2 class
-- statement:
--   The Group Coh construction uses the h2 Int Add Equiv symm apply eq H2 class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Characters.lean#L87-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Characters.lean#L87-L102

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_Characters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
variable (G : Type) [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply_eq_H2_class (χ : Additive G →+ AddCircle (1 : ℚ)) (y : G → ℚ)
    (hy : ∀ g : G, (y g : AddCircle (1 : ℚ)) = χ (Additive.ofMul g)) (x : G × G → ℤ)
    (hx : ∀ g h : G, (x (g, h) : ℚ) = y g + y h - y (g * h)) :
    ∃ hc : x ∈ cocycles₂ (Rep.trivial ℤ G ℤ),
      (h2IntAddEquiv G).symm χ = H2π (Rep.trivial ℤ G ℤ) ⟨x, hc⟩ := by sorry
