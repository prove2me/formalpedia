-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coeffToRegular_eq_zero_iff
-- name    : GroundTheory.ProfCoh.coeffToRegular_eq_zero_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:28.617468+00:00
-- url     : https://prove2.me/theorems/de4a8d29-d0ad-4384-8aa8-431cee1d148d
-- title:
--   Prof Coh: coeff To Regular eq zero iff
-- statement:
--   The Prof Coh construction uses the coeff To Regular eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L334-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L334-L352

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
variable {Γ O : Type*} [Fintype Γ] [AddCommGroup O] {p n : ℕ}
  (b : Module.Basis (Fin n) (ZMod p) (ModN O p))

theorem GroundTheory.ProfCoh.coeffToRegular_eq_zero_iff (c : Γ → O) :
    coeffToRegular b c = 0 ↔ c ∈ LinearMap.range (LinearMap.lsmul ℤ (Γ → O) p) := by sorry
