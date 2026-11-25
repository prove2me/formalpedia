-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_normalSubEquiv_apply
-- name    : GroundTheory.ProfCoh.normalSubEquiv_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:42.496031+00:00
-- url     : https://prove2.me/theorems/a651d4b3-f4f3-4dbb-aff2-201530d98934
-- title:
--   Prof Coh: normal Sub Equiv apply
-- statement:
--   The Prof Coh construction uses the normal Sub Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L302-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L302-L304

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
variable [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension E F]
attribute [local instance] integerAction
attribute [local instance] normalSubAction
variable {θ : F} (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ)
  (hθO : ∀ σ : F ≃ₐ[E] F, σ θ ∈ 𝒪[F])
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem GroundTheory.ProfCoh.normalSubEquiv_apply (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    normalSubEquiv hθ hθO c = normalSubOfCoeff hθO c := by sorry
