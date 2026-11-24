-- Prove2me | Theorems.Thm_GlobalTheory_T_rootExchangeUnipotent_haar_and_modulus
-- name    : GlobalTheory.T.rootExchangeUnipotent_haar_and_modulus
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:56:25.579519+00:00
-- url     : https://prove2.me/theorems/14491a88-3c72-4d6e-92f0-fd28776e7781
-- title:
--   T: root Exchange Unipotent haar and modulus
-- statement:
--   The T construction uses the root Exchange Unipotent haar and modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulusStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentHaarAndModulusStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rootExchangeUnipotent_haar_and_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure], IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) ∧ IsClosed (R k n c p : Set (GL (n ⊕ Fin c) k)) ∧ (volN ν n c p).IsHaarMeasure ∧ (volN ν n c p).IsMulRightInvariant ∧ ∀ (x : GL n k) (f : GL (n ⊕ Fin c) k → ℂ), ∫ u : N k n c p, f (embX c x * (u : GL (n ⊕ Fin c) k) * (embX c x)⁻¹) ∂(volN ν n c p) = (nabs k (Matrix.GeneralLinearGroup.det x) ^ (-((c : ℝ) + 1 - 2 * p))) • ∫ u : N k n c p, f u ∂(volN ν n c p) := by sorry
