-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitToModN_eq_zero_iff
-- name    : GroundTheory.ProfCoh.unitToModN_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:58.048061+00:00
-- url     : https://prove2.me/theorems/3291e7c7-ab4e-451a-a473-788bda1d1207
-- title:
--   Prof Coh: unit To Mod N eq zero iff
-- statement:
--   The Prof Coh construction uses the unit To Mod N eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L179-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L179-L203

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

theorem GroundTheory.ProfCoh.unitToModN_eq_zero_iff (hp : p.Prime) {k : ℕ} (hk : e + 1 ≤ k)
    (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe (Nat.le_of_succ_le hk) u = 0 ↔
      u ∈ LinearMap.range (LinearMap.lsmul ℤ (Additive (unitFiltration F k)) p) := by sorry
