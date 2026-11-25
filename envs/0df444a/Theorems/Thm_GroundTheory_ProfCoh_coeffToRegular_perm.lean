-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coeffToRegular_perm
-- name    : GroundTheory.ProfCoh.coeffToRegular_perm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:19.811958+00:00
-- url     : https://prove2.me/theorems/eaf31ca8-e496-43da-b9b6-9923201872a4
-- title:
--   Prof Coh: coeff To Regular perm
-- statement:
--   The Prof Coh construction uses the coeff To Regular perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L366-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L366-L385

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

theorem GroundTheory.ProfCoh.coeffToRegular_perm [Group Γ] (τ : Γ) (c : Γ → O) :
    coeffToRegular b (fun σ ↦ c (τ⁻¹ * σ)) =
      piRep (Fin n) (Representation.leftRegular (ZMod p) Γ) τ (coeffToRegular b c) := by sorry
