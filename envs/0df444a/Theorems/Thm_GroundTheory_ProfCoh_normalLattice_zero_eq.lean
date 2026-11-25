-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_normalLattice_zero_eq
-- name    : GroundTheory.ProfCoh.normalLattice_zero_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:29.559794+00:00
-- url     : https://prove2.me/theorems/e4cc1cf1-3021-42d7-aea5-b13674c4b387
-- title:
--   Prof Coh: normal Lattice zero eq
-- statement:
--   The Prof Coh construction uses the normal Lattice zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L237-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L237-L239

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
variable {E F : Type*} [Field E] [ValuativeRel E] [Field F] [ValuativeRel F] [Algebra E F]
  [FiniteDimensional E F]
omit [ValuativeRel F] [FiniteDimensional E F]

theorem GroundTheory.ProfCoh.normalLattice_zero_eq (π : 𝒪[E]) (θ : F) :
    normalLattice π θ 0 = normalLattice (1 : 𝒪[E]) θ 0 := by sorry
