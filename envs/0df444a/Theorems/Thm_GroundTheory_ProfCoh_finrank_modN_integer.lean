-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finrank_modN_integer
-- name    : GroundTheory.ProfCoh.finrank_modN_integer
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:50:14.921054+00:00
-- url     : https://prove2.me/theorems/7af4dc58-fb34-480f-823c-76c2c97f1622
-- title:
--   Prof Coh: finrank mod N integer
-- statement:
--   The Prof Coh construction uses the finrank mod N integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L199-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L199-L208

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {p : ℕ}
variable [Fact p.Prime]
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E]

theorem GroundTheory.ProfCoh.finrank_modN_integer {n : ℕ} (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n) :
    Finite (ModN 𝒪[E] p) ∧ Module.finrank (ZMod p) (ModN 𝒪[E] p) = n := by sorry
