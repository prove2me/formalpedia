-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoExp_abs_norm_eq_prod
-- name    : GlobalTheory.HeckeTwoExp.abs_norm_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:51.655628+00:00
-- url     : https://prove2.me/theorems/968c7645-3c83-476b-b7db-c2263382fb0b
-- title:
--   Hecke Two Exp: abs norm eq prod
-- statement:
--   The Hecke Two Exp construction uses the abs norm eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsNormEqProd.lean#L34-L40

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

theorem GlobalTheory.HeckeTwoExp.abs_norm_eq_prod [IsTotallyReal F] (ν : F) :
    ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) = ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ) := by sorry
