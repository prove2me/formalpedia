-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_VolN_volN_haar_and_modulus
-- name    : GlobalTheory.RootEx.VolN.volN_haar_and_modulus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:38.714517+00:00
-- url     : https://prove2.me/theorems/cf3987f9-545a-4c69-b07c-dd216e617437
-- title:
--   Vol N: vol N haar and modulus
-- statement:
--   The Vol N construction uses the vol N haar and modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L466-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulus.lean#L466-L469

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

theorem GlobalTheory.RootEx.VolN.volN_haar_and_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure], IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) ∧ IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) ∧ (volN ν n c p).IsHaarMeasure ∧ (volN ν n c p).IsMulRightInvariant ∧ ∀ (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) = (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) • ∫ u : N k n c p, f u ∂(volN ν n c p) := by sorry
