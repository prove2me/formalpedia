-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_maximalIdeal_pow_add_iff
-- name    : GroundTheory.ProfCoh.mem_maximalIdeal_pow_add_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:45.409548+00:00
-- url     : https://prove2.me/theorems/8b196e17-6ea1-4cf4-ab0c-02f64703a439
-- title:
--   Prof Coh: mem maximal Ideal pow add iff
-- statement:
--   The Prof Coh construction uses the mem maximal Ideal pow add iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L107-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L107-L121

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
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
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable (E F : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
attribute [local instance] integerAction
attribute [local instance] unitFiltrationAction maxPowAction
variable {E F}
variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p : ℕ} {e : ℕ} {ε : 𝒪[F]ˣ}
  (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe

theorem GroundTheory.ProfCoh.mem_maximalIdeal_pow_add_iff {k : ℕ} {x : 𝒪[F]} :
    x ∈ 𝓂[F] ^ (k + e) ↔ ∃ y ∈ 𝓂[F] ^ k, x = p * y := by sorry
