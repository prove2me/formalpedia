-- Prove2me | Theorems.Thm_GordanGenProof_fm_vec
-- name    : GordanGenProof.fm_vec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:41.115044+00:00
-- url     : https://prove2.me/theorems/35995a98-7251-47ce-8cd2-675ac4a7ecea
-- title:
--   Gordan Gen Proof: fm vec
-- statement:
--   The Gordan Gen Proof construction uses the fm vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L131-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L131-L154

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset

theorem GordanGenProof.fm_vec {n : ℕ} (P : Finset ((Fin n → ℚ) × ℚ)) (x : Fin n → ℚ) :
    (∃ t : ℚ, ∀ p ∈ P, 0 ≤ p.1 ⬝ᵥ x + p.2 * t) ↔ x ∈ hcone (fmSet P) id := by sorry
