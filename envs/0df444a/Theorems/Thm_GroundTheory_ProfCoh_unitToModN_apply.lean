-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitToModN_apply
-- name    : GroundTheory.ProfCoh.unitToModN_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:38.374541+00:00
-- url     : https://prove2.me/theorems/b40d40a8-602c-4fb1-8c43-0bc25596a66e
-- title:
--   Prof Coh: unit To Mod N apply
-- statement:
--   The Prof Coh construction uses the unit To Mod N apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L158-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L158-L162

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

theorem GroundTheory.ProfCoh.unitToModN_apply (hϖ : Irreducible ϖ) (hpe : (p : 𝒪[F]) = ϖ ^ e * ε) {k : ℕ} (hk : e ≤ k)
    (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe hk u =
      Submodule.Quotient.mk ⟨((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) - 1, sub_one_mem_maxPow u.toMul⟩ := by sorry
