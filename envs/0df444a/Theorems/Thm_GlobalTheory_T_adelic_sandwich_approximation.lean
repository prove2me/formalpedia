-- Prove2me | Theorems.Thm_GlobalTheory_T_adelic_sandwich_approximation
-- name    : GlobalTheory.T.adelic_sandwich_approximation
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:51.454261+00:00
-- url     : https://prove2.me/theorems/f6fd7309-281d-41a6-b02b-f6016cb35221
-- title:
--   T: adelic sandwich approximation
-- statement:
--   The T construction uses the adelic sandwich approximation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TruncatedSumLimitStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TruncatedSumLimitStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
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

theorem GlobalTheory.T.adelic_sandwich_approximation : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) → Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by sorry
