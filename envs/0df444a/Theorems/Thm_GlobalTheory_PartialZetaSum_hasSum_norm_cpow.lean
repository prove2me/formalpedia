-- Prove2me | Theorems.Thm_GlobalTheory_PartialZetaSum_hasSum_norm_cpow
-- name    : GlobalTheory.PartialZetaSum.hasSum_norm_cpow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:21.215175+00:00
-- url     : https://prove2.me/theorems/59042b4b-4c4a-47b8-a04a-64cf79a26a1b
-- title:
--   Partial Zeta Sum: has Sum norm cpow
-- statement:
--   The Partial Zeta Sum construction uses the has Sum norm cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumAbsNormCpowUnitClassesPartialZeta.lean#L112-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumAbsNormCpowUnitClassesPartialZeta.lean#L112-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.PartialZetaSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.PartialZetaSum.hasSum_norm_cpow : ∀ (F : Type) [Field F] [NumberField F] (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ s : ℂ, 1 < s.re → HasSum (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-s)) (((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔟 : ℝ) : ℂ) ^ (-s) * Zb s) := by sorry
