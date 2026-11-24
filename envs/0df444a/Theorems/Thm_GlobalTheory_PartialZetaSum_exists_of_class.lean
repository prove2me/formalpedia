-- Prove2me | Theorems.Thm_GlobalTheory_PartialZetaSum_exists_of_class
-- name    : GlobalTheory.PartialZetaSum.exists_of_class
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:16.64366+00:00
-- url     : https://prove2.me/theorems/fe58b45a-000d-47a1-9acd-db368c223cbd
-- title:
--   Partial Zeta Sum: exists of class
-- statement:
--   The Partial Zeta Sum construction uses the exists of class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumAbsNormCpowUnitClassesPartialZeta.lean#L72-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumAbsNormCpowUnitClassesPartialZeta.lean#L72-L100

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

theorem GlobalTheory.PartialZetaSum.exists_of_class (𝔟 : Frac F) (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = (ClassGroup.mk F 𝔟)⁻¹) :
    ∃ b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F), idealOf 𝔟 b = J.1 := by sorry
