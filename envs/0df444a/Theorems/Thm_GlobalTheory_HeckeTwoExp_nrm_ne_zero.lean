-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoExp_nrm_ne_zero
-- name    : GlobalTheory.HeckeTwoExp.nrm_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:37.185482+00:00
-- url     : https://prove2.me/theorems/262ed687-8a61-4af9-9c9c-b8661d81b087
-- title:
--   Hecke Two Exp: nrm ne zero
-- statement:
--   The Hecke Two Exp construction uses the nrm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L137-L140

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

theorem GlobalTheory.HeckeTwoExp.nrm_ne_zero (𝔞 : Frac F) : nrm 𝔞 ≠ 0 := by sorry
