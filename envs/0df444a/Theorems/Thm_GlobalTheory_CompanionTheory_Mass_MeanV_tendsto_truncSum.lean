-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tendsto_truncSum
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:19:26.584555+00:00
-- url     : https://prove2.me/theorems/86997f71-d99f-4698-bc35-7dfe6b4e642e
-- title:
--   Mean V: tendsto trunc Sum
-- statement:
--   The Mean V construction uses the tendsto trunc Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TruncatedSumLimit.lean#L35-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TruncatedSumLimit.lean#L35-L82

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimit
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV

theorem GlobalTheory.CompanionTheory.Mass.MeanV.tendsto_truncSum : Equi → CountBd → ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ (li : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ T, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    Tendsto (truncSum θ G T ψ) (𝓝[>] 0) (𝓝 ((∫ y, G y ∂li) * ∏ v ∈ T, ∫ s, ψ v s ∂(lam v))) := by sorry
