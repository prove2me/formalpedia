-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_contDiffOn_hTrans
-- name    : GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:53.559796+00:00
-- url     : https://prove2.me/theorems/e13f6423-2957-4c45-9bd8-6241a18ff1c1
-- title:
--   Term Smooth: cont Diff On h Trans
-- statement:
--   The Term Smooth construction uses the cont Diff On h Trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L195-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L195-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth

theorem GlobalTheory.HeckeTwo.TermSmooth.contDiffOn_hTrans (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) :
    ContDiffOn ℝ ∞ (hTrans σ ν) {y | y ≠ 0} := by sorry
