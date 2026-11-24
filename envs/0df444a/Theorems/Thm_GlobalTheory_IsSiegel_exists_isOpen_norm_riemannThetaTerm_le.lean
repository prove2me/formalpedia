-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_exists_isOpen_norm_riemannThetaTerm_le
-- name    : GlobalTheory.IsSiegel.exists_isOpen_norm_riemannThetaTerm_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:22:24.2608+00:00
-- url     : https://prove2.me/theorems/7042155b-62f1-4f3c-833f-3b99d96aa8b4
-- title:
--   Is Siegel: exists is Open norm riemann Theta Term le
-- statement:
--   The Is Siegel construction uses the exists is Open norm riemann Theta Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L49-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.IsSiegel.exists_isOpen_norm_riemannThetaTerm_le {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : ∃ U : Set ((ι → ℂ) × (ι → ι → ℂ)), IsOpen U ∧ (v, of.symm Ω) ∈ U ∧
      ∃ u : (ι → ℤ) → ℝ, Summable u ∧
        ∀ n, ∀ p ∈ U, ‖riemannThetaTerm a b (of p.2) p.1 n‖ ≤ u n := by sorry
