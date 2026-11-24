-- Prove2me | Theorems.Thm_GlobalTheory_SW_exists_int_div_of_intM
-- name    : GlobalTheory.SW.exists_int_div_of_intM
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:05.299815+00:00
-- url     : https://prove2.me/theorems/c82843ca-6f4d-43e0-97a1-c51621710ee0
-- title:
--   SW: exists int div of int M
-- statement:
--   The SW construction uses the exists int div of int M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EqOfSiegelThetaSeriesRationalEq.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EqOfSiegelThetaSeriesRationalEq.lean#L10-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.exists_int_div_of_intM {κ ι : Type} (R S : ℕ) (hR : 0 < R) (hS : 0 < S)
    (x : Matrix κ ι ℚ) (h : IntM ((R : ℚ) • x)) :
    ∃ s : κ × ι → ℤ, (Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)) = x := by sorry
