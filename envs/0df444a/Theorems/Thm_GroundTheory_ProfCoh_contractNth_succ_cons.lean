-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_contractNth_succ_cons
-- name    : GroundTheory.ProfCoh.contractNth_succ_cons
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:54.91821+00:00
-- url     : https://prove2.me/theorems/3f3a544e-0e2b-4fab-a31f-86bbbb824307
-- title:
--   Prof Coh: contract Nth succ cons
-- statement:
--   The Prof Coh construction uses the contract Nth succ cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean#L26-L42

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

theorem GroundTheory.ProfCoh.contractNth_succ_cons (op : α → α → α) (x : α) (g : Fin (n + 1) → α) (j : Fin (n + 1)) :
    Fin.contractNth j.succ op (Fin.cons x g : Fin (n + 2) → α) =
      Fin.cons x (Fin.contractNth j op g) := by sorry
