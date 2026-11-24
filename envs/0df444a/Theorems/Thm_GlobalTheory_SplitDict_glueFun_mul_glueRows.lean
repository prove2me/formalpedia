-- Prove2me | Theorems.Thm_GlobalTheory_SplitDict_glueFun_mul_glueRows
-- name    : GlobalTheory.SplitDict.glueFun_mul_glueRows
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:56.178741+00:00
-- url     : https://prove2.me/theorems/aecefda8-a6ee-412e-a704-40785825875a
-- title:
--   Split Dict: glue Fun mul glue Rows
-- statement:
--   The Split Dict construction uses the glue Fun mul glue Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L335-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBoxInvariantSnd.lean#L335-L338

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
  [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v] [DecidableEq τ] [DecidableEq w]

theorem GlobalTheory.SplitDict.glueFun_mul_glueRows (η' : Matrix ρ τ k) (η₀ : Matrix ρ w k) (ηd : Matrix ρ τ k)
    (r : Matrix τ v k) (x : Matrix w v k) (ys : Matrix τ v k) :
    glueFun η' η₀ ηd * glueRows r x ys = η' * r + (η₀ * x + ηd * ys) := by sorry
