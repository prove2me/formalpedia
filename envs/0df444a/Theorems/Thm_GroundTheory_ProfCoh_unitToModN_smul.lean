-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitToModN_smul
-- name    : GroundTheory.ProfCoh.unitToModN_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:52:24.893948+00:00
-- url     : https://prove2.me/theorems/87f0ec7f-a7bf-4a30-8997-03776fe56001
-- title:
--   Prof Coh: unit To Mod N smul
-- statement:
--   The Prof Coh construction uses the unit To Mod N smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L208-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L208-L216

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
omit hϖ hpe
variable (ϖ)

theorem GroundTheory.ProfCoh.unitToModN_smul (hϖ : Irreducible ϖ) (hpe : (p : 𝒪[F]) = ϖ ^ e * ε) {k : ℕ}
    (hk : e ≤ k) (σ : F ≃ₐ[E] F) (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe hk (σ • u) =
      modNRep (F ≃ₐ[E] F) (maxPow F k) p σ (unitToModN hϖ hpe hk u) := by sorry
