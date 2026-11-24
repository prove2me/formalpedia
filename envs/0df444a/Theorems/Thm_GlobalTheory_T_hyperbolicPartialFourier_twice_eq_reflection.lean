-- Prove2me | Theorems.Thm_GlobalTheory_T_hyperbolicPartialFourier_twice_eq_reflection
-- name    : GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:13.011807+00:00
-- url     : https://prove2.me/theorems/45a23cc0-2883-420b-a9df-64d408633673
-- title:
--   T: hyperbolic Partial Fourier twice eq reflection
-- statement:
--   The T construction uses the hyperbolic Partial Fourier twice eq reflection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HyperbolicPartialFourierTwiceEqReflectionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HyperbolicPartialFourierTwiceEqReflectionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierTwiceEqReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HyperbolicPartialFourierTwiceEqReflectionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by sorry
