-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_mem_cyclotomic_layer_prime_rpow
-- name    : GlobalTheory.T.norm_mem_cyclotomic_layer_prime_rpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:39.641567+00:00
-- url     : https://prove2.me/theorems/a7a3e818-2323-4191-95fd-e3771bc64a7e
-- title:
--   T: norm mem cyclotomic layer prime rpow
-- statement:
--   The T construction uses the norm mem cyclotomic layer prime rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormMemCyclotomicLayerPrimeRpowStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormMemCyclotomicLayerPrimeRpowStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpow
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_mem_cyclotomic_layer_prime_rpow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j → ∀ x : Om l, x ∈ Ks K j → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by sorry
