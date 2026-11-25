-- Prove2me | Theorems.Thm_GlobalTheory_T_heckePhiFourierConstantAtZero_differentiableOn
-- name    : GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:45:47.97623+00:00
-- url     : https://prove2.me/theorems/31244a78-4051-41e1-b112-6b7d93d132a0
-- title:
--   T: hecke Phi Fourier Constant At Zero differentiable On
-- statement:
--   The T construction uses the hecke Phi Fourier Constant At Zero differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOnStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOnStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOnStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heckePhiFourierConstantAtZero_differentiableOn : DifferentiableOn ℂ GlobalTheory.HeckeTwo.cConst GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.halfPlane := by sorry
