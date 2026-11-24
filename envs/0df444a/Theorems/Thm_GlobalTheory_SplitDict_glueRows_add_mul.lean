-- Prove2me | Theorems.Thm_GlobalTheory_SplitDict_glueRows_add_mul
-- name    : GlobalTheory.SplitDict.glueRows_add_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:32.866387+00:00
-- url     : https://prove2.me/theorems/f751f1bc-6068-4a58-8e6a-49488a14022f
-- title:
--   Split Dict: glue Rows add mul
-- statement:
--   The Split Dict construction uses the glue Rows add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L342-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L342-L345

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBoxInvariantSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitDict
variable {k : Type} [Field k]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable (ψ : AddChar k Circle) (m : Measure k) [m.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (s₁ s₂ : ℤˣ)
variable {ρ v τ w W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
  [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w] [Fintype W] [DecidableEq W]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  [DecidableEq ρ] [Fintype v] [DecidableEq v] [Fintype τ] [DecidableEq τ] [Fintype w] [DecidableEq w]

theorem GlobalTheory.SplitDict.glueRows_add_mul (r : Matrix τ v k) (x : Matrix w v k) (ys : Matrix τ v k)
    (ξ' : Matrix τ ρ k) (ξ₀ : Matrix w ρ k) (ν' : Matrix ρ v k) :
    glueRows r x ys + glueRows ξ' ξ₀ 0 * ν' = glueRows (r + ξ' * ν') (x + ξ₀ * ν') ys := by sorry
