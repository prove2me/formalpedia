-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_g_integerUnits_eq
-- name    : GroundTheory.ProfCoh.g_integerUnits_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:36.883208+00:00
-- url     : https://prove2.me/theorems/c2bb2984-47fa-4d4e-b007-5b627abf01f6
-- title:
--   Prof Coh: g integer Units eq
-- statement:
--   The Prof Coh construction uses the g integer Units eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L372-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L372-L446

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10

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
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [IsGalois E F]
  {l : ℕ} [Fact l.Prime] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))
attribute [local instance] integerAction unitFiltrationAction maxPowAction normalSubAction

theorem GroundTheory.ProfCoh.g_integerUnits_eq (hl : (l : F) ≠ 0) {n : ℕ}
    (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(l : 𝒪[E])}) = l ^ n) :
    Finite (ModN (Additive 𝒪[F]ˣ) l) ∧
      d.g (Additive 𝒪[F]ˣ) = n * d.toFun (MonoidAlgebra (ZMod l) (F ≃ₐ[E] F))
        (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) := by sorry
