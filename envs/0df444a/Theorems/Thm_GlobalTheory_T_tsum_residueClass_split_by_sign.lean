-- Prove2me | Theorems.Thm_GlobalTheory_T_tsum_residueClass_split_by_sign
-- name    : GlobalTheory.T.tsum_residueClass_split_by_sign
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:58.315986+00:00
-- url     : https://prove2.me/theorems/c6982929-56ca-410a-90fb-b25a9dd9033e
-- title:
--   T: tsum residue Class split by sign
-- statement:
--   The T construction uses the tsum residue Class split by sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumResidueClassSplitBySignStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TsumResidueClassSplitBySignStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumResidueClassSplitBySign
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumResidueClassSplitBySignStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tsum_residueClass_split_by_sign : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (R : ℤ → ℂ), Summable (fun n : ℤ => R ((r.val : ℤ) + n * N)) → ∑' n : ℤ, R ((r.val : ℤ) + n * N) = (if r = 0 then R 0 else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = r then R ((d : ℕ) : ℤ) else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = -r then R (-((d : ℕ) : ℤ)) else 0) := by sorry
