-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_integerUnits
-- name    : GroundTheory.ProfCoh.finite_torsN_integerUnits
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:45.302326+00:00
-- url     : https://prove2.me/theorems/74d0eb97-c7b5-4ba8-9e7c-a5d74cd71733
-- title:
--   Prof Coh: finite tors N integer Units
-- statement:
--   The Prof Coh construction uses the finite tors N integer Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L282-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L282-L295

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
omit [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem GroundTheory.ProfCoh.finite_torsN_integerUnits (l : ℕ) [NeZero l] : Finite (TorsN (Additive 𝒪[F]ˣ) l) := by sorry
