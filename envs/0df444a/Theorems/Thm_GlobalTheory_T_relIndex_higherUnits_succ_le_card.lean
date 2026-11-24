-- Prove2me | Theorems.Thm_GlobalTheory_T_relIndex_higherUnits_succ_le_card
-- name    : GlobalTheory.T.relIndex_higherUnits_succ_le_card
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:06.948823+00:00
-- url     : https://prove2.me/theorems/9b00e088-3dd5-4740-be7d-42fe447f959a
-- title:
--   T: rel Index higher Units succ le card
-- statement:
--   The T construction uses the rel Index higher Units succ le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexHigherUnitsSuccLeCardStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/RelIndexHigherUnitsSuccLeCardStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCardStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.relIndex_higherUnits_succ_le_card : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) → (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧ (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by sorry
