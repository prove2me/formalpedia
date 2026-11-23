-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- name    : GroundTheory.ProfCoh.mem_stabilizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:07.979131+00:00
-- url     : https://prove2.me/theorems/58aa2fd6-7065-48cd-aa8a-6dc9d006119e
-- title:
--   Prof Coh: mem stabilizer
-- statement:
--   The Prof Coh construction uses the mem stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules.lean#L25-L27

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]

theorem GroundTheory.ProfCoh.mem_stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (v : V) (g : G) : g ∈ stabilizer ρ v ↔ ρ g v = v := by sorry
