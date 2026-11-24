-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_integral_conj_volN
-- name    : GlobalTheory.RootEx.VolN.integral_conj_volN
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:56.016639+00:00
-- url     : https://prove2.me/theorems/71f81fac-8bae-4109-a945-c15e7ca5ef9d
-- title:
--   Vol N: integral conj vol N
-- statement:
--   The Vol N construction uses the integral conj vol N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L440-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L440-L462

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.RootEx.VolN.integral_conj_volN {p : ℕ} (h1 : 1 ≤ p) (hp : p ≤ c) (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ) :
    ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) =
      (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) •
        ∫ u : N k n c p, f u ∂(volN ν n c p) := by sorry
