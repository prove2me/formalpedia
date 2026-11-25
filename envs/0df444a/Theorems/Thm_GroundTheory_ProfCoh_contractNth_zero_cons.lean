-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_contractNth_zero_cons
-- name    : GroundTheory.ProfCoh.contractNth_zero_cons
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:29.724877+00:00
-- url     : https://prove2.me/theorems/848f7f82-b91a-4be2-9ea2-50d70a19221f
-- title:
--   Prof Coh: contract Nth zero cons
-- statement:
--   The Prof Coh construction uses the contract Nth zero cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean#L16-L24

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology Filter Topology
universe u
variable {α : Type*} {n : ℕ}

theorem GroundTheory.ProfCoh.contractNth_zero_cons (op : α → α → α) (x : α) (g : Fin (n + 1) → α) :
    Fin.contractNth 0 op (Fin.cons x g : Fin (n + 2) → α) =
      Fin.cons (op x (g 0)) (fun i => g i.succ) := by sorry
