-- Prove2me | Theorems.Thm_GlobalTheory_T_flat_of_flat_comp_of_map_maximalIdeal_eq
-- name    : GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:32:27.97949+00:00
-- url     : https://prove2.me/theorems/18501ca6-f451-44e7-b0ea-ef8649682746
-- title:
--   T: flat of flat comp of map maximal Ideal eq
-- statement:
--   The T construction uses the flat of flat comp of map maximal Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdealStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomFlatOfCompFlatOfMapMaximalIdealStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdeal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomFlatOfCompFlatOfMapMaximalIdealStatement
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq : ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E] (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' → IsLocalHom b → (b.comp φ').Flat → b.Flat := by sorry
