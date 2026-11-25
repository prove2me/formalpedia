-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_modN_maxPow
-- name    : GroundTheory.ProfCoh.finite_modN_maxPow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:35.782886+00:00
-- url     : https://prove2.me/theorems/44406e30-9157-40d8-84d9-cb29b8970e10
-- title:
--   Prof Coh: finite mod N max Pow
-- statement:
--   The Prof Coh construction uses the finite mod N max Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L236-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L236-L257

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p e : ℕ} {ε : 𝒪[F]ˣ} (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe

theorem GroundTheory.ProfCoh.finite_modN_maxPow (k : ℕ) : Finite (ModN (maxPow F k) p) := by sorry
