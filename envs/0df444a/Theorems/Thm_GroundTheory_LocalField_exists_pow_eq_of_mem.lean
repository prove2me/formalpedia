-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_pow_eq_of_mem
-- name    : GroundTheory.LocalField.exists_pow_eq_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:46.575127+00:00
-- url     : https://prove2.me/theorems/d2af47fe-1d1e-4a6b-b44b-ca173e3441a0
-- title:
--   Local Field: exists pow eq of mem
-- statement:
--   The Local Field construction uses the exists pow eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L156-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L156-L172

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.exists_pow_eq_of_mem {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {m k : ℕ} (hm : m ≠ 0)
    {ε : 𝒪[K]ˣ} (hmk : (m : 𝒪[K]) = ϖ ^ k * ε) {w : 𝒪[K]ˣ}
    (hw : w ∈ unitFiltration K (2 * k + 1)) : ∃ x : 𝒪[K]ˣ, x ^ m = w := by sorry
