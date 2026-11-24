-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_uniformiser_split_place_cm_order_nonunit
-- name    : GlobalTheory.T.exists_uniformiser_split_place_cm_order_nonunit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:38:04.945698+00:00
-- url     : https://prove2.me/theorems/b3dc4d0a-1bed-4e2a-a917-3b06802c6bbf
-- title:
--   T: exists uniformiser split place cm order nonunit
-- statement:
--   The T construction uses the exists uniformiser split place cm order nonunit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunitStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniformiserSplitPlaceCmOrderNonunitStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniformiserSplitPlaceCmOrderNonunit
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniformiserSplitPlaceCmOrderNonunitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_uniformiser_split_place_cm_order_nonunit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by sorry
