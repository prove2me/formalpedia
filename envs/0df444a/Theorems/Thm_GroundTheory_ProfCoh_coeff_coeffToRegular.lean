-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coeff_coeffToRegular
-- name    : GroundTheory.ProfCoh.coeff_coeffToRegular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:54.070051+00:00
-- url     : https://prove2.me/theorems/131a7df5-9632-42a0-8cc5-c4e0bac0c1ad
-- title:
--   Prof Coh: coeff coeff To Regular
-- statement:
--   The Prof Coh construction uses the coeff coeff To Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L329-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean#L329-L332

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

theorem GroundTheory.ProfCoh.coeff_coeffToRegular (c : Γ → O) (i : Fin n) (τ : Γ) :
    (coeffToRegular b c i).coeff τ = b.repr (Submodule.Quotient.mk (c τ)) i := by sorry
