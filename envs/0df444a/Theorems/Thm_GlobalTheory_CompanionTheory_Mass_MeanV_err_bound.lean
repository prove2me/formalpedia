-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_err_bound
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.err_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:27.219796+00:00
-- url     : https://prove2.me/theorems/8b1d798d-9dad-4d69-924e-2862d951c3ac
-- title:
--   Mean V: err bound
-- statement:
--   The Mean V construction uses the err bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeanValueFormula.lean#L177-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MeanValueFormula.lean#L177-L328

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteProductDifferenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TailSumOverPlacesSmallStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultipliableLocalFactorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalFactorSandwichApproxStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EulerProductConvergenceBoundStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalHaarMeasureSingletonStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeanValueFormula
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

theorem GlobalTheory.CompanionTheory.Mass.MeanV.err_bound (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hG : Continuous G)
    (hGc : HasCompactSupport G) (hG0 : ∀ y, 0 ≤ G y) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgS : ∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v))
    (hz : ∀ v, v ∉ S → ∀ s, s ∉ v.adicCompletionIntegers F → g v s = 0)
    (hb1 : ∀ v, v ∉ S → ∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ))
    (hb2 : ∀ v, v ∉ S → ∀ s : Fv F v, Valued.v s = 1 → |g v s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T₀ ∧ ∀ T, T₀ ⊆ T → ∀ δ : ℝ, 0 < δ →
      |fullSum θ G g δ - truncSum θ G T g δ| ≤ η := by sorry
