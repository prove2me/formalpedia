-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_hasDerivAt_intT
-- name    : GlobalTheory.HeckeTwo.TermSmooth.hasDerivAt_intT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:02:16.049351+00:00
-- url     : https://prove2.me/theorems/a10839b9-40b4-4f60-8f33-2eda0a6c25b5
-- title:
--   Term Smooth: has Deriv At int T
-- statement:
--   The Term Smooth construction uses the has Deriv At int T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L120-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContDiffOnHeckeEisensteinFourierTerm.lean#L120-L158

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

theorem GlobalTheory.HeckeTwo.TermSmooth.hasDerivAt_intT (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) {a b : ℕ} (m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) :
    HasDerivAt (intT σ ν a b m)
      (-(a : ℂ) * I * intT σ ν (a + 1) b m y₀ + 2 * (-σ - (b : ℂ)) * intT σ ν a (b + 1) (m + 1) y₀
        + (m : ℂ) * intT σ ν a b (m - 1) y₀) y₀ := by sorry
