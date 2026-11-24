-- Prove2me | Theorems.Thm_GlobalTheory_Proof_hilbertEisensteinLatticeSummand_weightTwo_bound_normSq_lower
-- name    : GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.normSq_lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:13.81812+00:00
-- url     : https://prove2.me/theorems/5fca112f-eeab-43ef-a11b-54d6af07dbed
-- title:
--   hilbert Eisenstein Lattice Summand weight Two bound: norm Sq lower
-- statement:
--   The hilbert Eisenstein Lattice Summand weight Two bound construction uses the norm Sq lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeSummandWeightTwoBound.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinLatticeSummandWeightTwoBound.lean#L14-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeSummandWeightTwoBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound

theorem GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.normSq_lower (w : ℂ) (a b : ℝ) :
    (w.im) ^ 2 / (1 + ‖w‖ ^ 2) * (a ^ 2 + b ^ 2) ≤ ‖(a : ℂ) + b * w‖ ^ 2 := by sorry
