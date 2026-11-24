-- Prove2me | Theorems.Thm_GlobalTheory_T_local_factor_sandwich_approx
-- name    : GlobalTheory.T.local_factor_sandwich_approx
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:52:37.052805+00:00
-- url     : https://prove2.me/theorems/0779e289-ae00-4535-95e5-302dc5fc51fd
-- title:
--   T: local factor sandwich approx
-- statement:
--   The T construction uses the local factor sandwich approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFactorSandwichApproxStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalFactorSandwichApproxStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApprox
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApproxStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.local_factor_sandwich_approx : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by sorry
