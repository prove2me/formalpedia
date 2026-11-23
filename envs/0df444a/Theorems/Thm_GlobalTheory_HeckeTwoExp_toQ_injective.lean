-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoExp_toQ_injective
-- name    : GlobalTheory.HeckeTwoExp.toQ_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:48.971642+00:00
-- url     : https://prove2.me/theorems/a71d8fa2-a8bf-427a-8a6d-9ed8a68c5006
-- title:
--   Hecke Two Exp: to Q injective
-- statement:
--   The Hecke Two Exp construction uses the to Q injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L52-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
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
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HeckeTwoExp.toQ_injective (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by sorry
