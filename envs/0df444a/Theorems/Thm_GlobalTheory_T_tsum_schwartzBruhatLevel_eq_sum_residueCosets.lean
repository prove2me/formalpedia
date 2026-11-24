-- Prove2me | Theorems.Thm_GlobalTheory_T_tsum_schwartzBruhatLevel_eq_sum_residueCosets
-- name    : GlobalTheory.T.tsum_schwartzBruhatLevel_eq_sum_residueCosets
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:59:52.510869+00:00
-- url     : https://prove2.me/theorems/cd1056d5-de58-40ae-aabc-e40a91e75337
-- title:
--   T: tsum schwartz Bruhat Level eq sum residue Cosets
-- statement:
--   The T construction uses the tsum schwartz Bruhat Level eq sum residue Cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TsumSchwartzBruhatLevelEqSumResidueCosetsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TsumSchwartzBruhatLevelEqSumResidueCosetsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TsumSchwartzBruhatLevelEqSumResidueCosetsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tsum_schwartzBruhatLevel_eq_sum_residueCosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → Summable (fun x => φ x * F x) → ∑' x, φ x * F x = ∑ n : κ → ι → Fin (R * R), φ (rep R n) * ∑' m : κ → ι → ℤ, F (rep R n + (R : ℚ) • zm m) := by sorry
