-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_eq_cexp_fderiv_of_map_add
-- name    : GlobalTheory.Doubling.eq_cexp_fderiv_of_map_add
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:20.292872+00:00
-- url     : https://prove2.me/theorems/e133adc4-2497-5f81-a8b7-affd5cbec081
-- title:
--   Doubling: eq cexp fderiv of map add
-- statement:
--   The Doubling construction uses the eq cexp fderiv of map add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsBigOPowIffIteratedFDerivEqZero.lean#L36-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsBigOPowIffIteratedFDerivEqZero.lean#L36-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqExpFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsBigOPowIffIteratedFDerivEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate
open GlobalTheory GlobalTheory.Doubling
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.Doubling.eq_cexp_fderiv_of_map_add {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by sorry
