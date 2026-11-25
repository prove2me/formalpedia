-- Prove2me | Theorems.Thm_GlobalTheory_HCA_apOp_sum_coef
-- name    : GlobalTheory.HCA.apOp_sum_coef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:40.96914+00:00
-- url     : https://prove2.me/theorems/c4fb9bef-a89a-48f6-9cb9-7de93f68a0fd
-- title:
--   HCA: ap Op sum coef
-- statement:
--   The HCA construction uses the ap Op sum coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSumSquaresRightDerivPowDifferentialOperato.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSumSquaresRightDerivPowDifferentialOperato.lean#L12-L18

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSumSquaresRightDerivPowDifferentialOperato
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.apOp_sum_coef {d : ℕ} {ι : Type} (s : Finset ι) (m : ℕ) (a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (u : E d → ℂ) (x : E d) :
    apOp m (fun n w y => ∑ i ∈ s, a i n w y) u x = ∑ i ∈ s, apOp m (a i) u x := by sorry
