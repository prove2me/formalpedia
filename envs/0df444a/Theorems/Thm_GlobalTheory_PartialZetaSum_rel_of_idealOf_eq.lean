-- Prove2me | Theorems.Thm_GlobalTheory_PartialZetaSum_rel_of_idealOf_eq
-- name    : GlobalTheory.PartialZetaSum.rel_of_idealOf_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:08.804811+00:00
-- url     : https://prove2.me/theorems/b7100917-5874-4fec-b008-5046bb7d676c
-- title:
--   Partial Zeta Sum: rel of ideal Of eq
-- statement:
--   The Partial Zeta Sum construction uses the rel of ideal Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumAbsNormCpowUnitClassesPartialZeta.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumAbsNormCpowUnitClassesPartialZeta.lean#L56-L61

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

theorem GlobalTheory.PartialZetaSum.rel_of_idealOf_eq (𝔟 : Frac F) {b b' : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)}
    (h : idealOf 𝔟 b = idealOf 𝔟 b') : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r b b' := by sorry
