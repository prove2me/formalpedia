-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarAlg_exists_natCast_smul_intM
-- name    : GlobalTheory.SW.HaarAlg.exists_natCast_smul_intM
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:41:30.896888+00:00
-- url     : https://prove2.me/theorems/5ab1fdd0-f9f2-4374-b040-bb78982b9b97
-- title:
--   Haar Alg: exists nat Cast smul int M
-- statement:
--   The Haar Alg construction uses the exists nat Cast smul int M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L59-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/RationalSchwartzBruhatAlgebraIntegralLinear.lean#L59-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinear
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarAlg
variable {K : Type} [Field K] {κ ι : Type}

theorem GlobalTheory.SW.HaarAlg.exists_natCast_smul_intM [NumberField K] [Fintype κ] [Fintype ι] (b : Matrix κ ι K) :
    ∃ N : ℕ, 0 < N ∧ IntM ((N : K) • b) := by sorry
