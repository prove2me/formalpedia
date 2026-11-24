-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_exists_fixed_mem_span_orbit
-- name    : GroundTheory.GroupCoh.exists_fixed_mem_span_orbit
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:07.768791+00:00
-- url     : https://prove2.me/theorems/ae1cf49c-de94-4351-847d-c1ca89120e3b
-- title:
--   Group Coh: exists fixed mem span orbit
-- statement:
--   The Group Coh construction uses the exists fixed mem span orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFixed.lean#L13-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupFixed.lean#L13-L60

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupFixed
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
open Representation
variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]
  [AddCommGroup V] [Module k V]

theorem GroundTheory.GroupCoh.exists_fixed_mem_span_orbit (hG : IsPGroup p G) (ρ : Representation k G V) {m : V}
    (hm : m ≠ 0) :
    ∃ v ∈ Submodule.span k (Set.range fun g : G => ρ g m), v ≠ 0 ∧ ∀ g : G, ρ g v = v := by sorry
