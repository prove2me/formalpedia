-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_pi
-- name    : GroundTheory.Global.cycHerbrand_pi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:40:20.261161+00:00
-- url     : https://prove2.me/theorems/8a55b795-59c5-4813-9f0d-e56b4c71a90e
-- title:
--   Global: cyc Herbrand pi
-- statement:
--   The Global construction uses the cyc Herbrand pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L248-L253

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G ι : Type*} [CommRing k] [Group G] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)]
variable [Fintype G]

theorem GroundTheory.Global.cycHerbrand_pi [Fintype ι] (ρ : ∀ i, Representation k G (V i)) (σ : G) :
    cycHerbrand (piRep ρ) σ = ∏ i, cycHerbrand (ρ i) σ := by sorry
