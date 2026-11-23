-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_algEquiv_apply_eq_of_pow_prime_pow_apply_eq
-- name    : GroundTheory.ProfCoh.algEquiv_apply_eq_of_pow_prime_pow_apply_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:09.553604+00:00
-- url     : https://prove2.me/theorems/9ab3bde1-7e8e-4df0-92c3-9828530670af
-- title:
--   Prof Coh: alg Equiv apply eq of pow prime pow apply eq
-- statement:
--   The Prof Coh construction uses the alg Equiv apply eq of pow prime pow apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L278-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L278-L299

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
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
open GroundTheory.LocalField ValuativeRel IntermediateField

theorem GroundTheory.ProfCoh.algEquiv_apply_eq_of_pow_prime_pow_apply_eq {K L : Type*} [Field K] [Field L]
    [Algebra K L] {l : ℕ} (hl : l.Prime) {ζ : L} (hζ : ζ ^ l = 1) (σ : L ≃ₐ[K] L) {n : ℕ}
    (h : (σ ^ l ^ n) ζ = ζ) : σ ζ = ζ := by sorry
