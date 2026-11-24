-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_flat_of_comp_flat_of_map_maximalIdeal
-- name    : GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:24.826355+00:00
-- url     : https://prove2.me/theorems/78225960-6176-4e0e-a1d9-a7db81ae5baf
-- title:
--   Global Theory: ring Hom flat of comp flat of map maximal Ideal
-- statement:
--   The Global Theory construction uses the ring Hom flat of comp flat of map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L164-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdeal.lean#L164-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap IsLocalRing
open GlobalTheory

theorem GlobalTheory.ringHom_flat_of_comp_flat_of_map_maximalIdeal :
    ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
      [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E]
      (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' →
      IsLocalHom b → (b.comp φ').Flat → b.Flat := by sorry
