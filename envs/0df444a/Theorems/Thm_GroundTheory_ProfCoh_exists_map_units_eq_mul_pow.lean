-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_map_units_eq_mul_pow
-- name    : GroundTheory.ProfCoh.exists_map_units_eq_mul_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:39.175235+00:00
-- url     : https://prove2.me/theorems/62fa3329-dc60-40e5-b1db-35d0b0a83ae1
-- title:
--   Prof Coh: exists map units eq mul pow
-- statement:
--   The Prof Coh construction uses the exists map units eq mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/VanishingUnits.lean#L60-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/VanishingUnits.lean#L60-L120

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_VanishingUnits
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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.ProfCoh.exists_map_units_eq_mul_pow {l m : ℕ} (hl : (l : 𝓀[F]) ≠ 0) (σ : F ≃+* F)
    (hval : ∀ x : F, valuation F (σ x) = valuation F x)
    (hin : ∀ x : F, valuation F x ≤ 1 → valuation F (σ x - x) < 1)
    (hm : m.Coprime l) (hσm : ∀ x : F, σ^[m] x = x) (u : Fˣ) :
    ∃ y : Fˣ, Units.map (σ : F →* F) u = u * y ^ l := by sorry
