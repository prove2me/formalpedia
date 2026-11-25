-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finrank_invariants_leftRegular_tprod
-- name    : GroundTheory.ProfCoh.finrank_invariants_leftRegular_tprod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:53.383137+00:00
-- url     : https://prove2.me/theorems/8a6b3920-88be-5cc6-94c1-f2f7bc95337e
-- title:
--   Prof Coh: finrank invariants left Regular tprod
-- statement:
--   The Prof Coh construction uses the finrank invariants left Regular tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/CoprimeRegular.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/CoprimeRegular.lean#L93-L95

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_CoprimeRegular
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
open Representation TensorProduct
variable {k Γ N : Type*} [CommRing k] [Group Γ] [Fintype Γ] [DecidableEq Γ] [AddCommGroup N]
  [Module k N] (σ : Representation k Γ N)

theorem GroundTheory.ProfCoh.finrank_invariants_leftRegular_tprod :
    Module.finrank k ((leftRegular k Γ).tprod σ).invariants = Module.finrank k N := by sorry
