-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_support_finite
-- name    : GlobalTheory.CompanionTheory.Mass.MeanV.support_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:55.710808+00:00
-- url     : https://prove2.me/theorems/a6db80b2-7a06-4e03-adf8-3514e387b93d
-- title:
--   Mean V: support finite
-- statement:
--   The Mean V construction uses the support finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TsumNeZeroEqSum.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TsumNeZeroEqSum.lean#L10-L21

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsIntegralMultipleBoundedPlacesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
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

theorem GlobalTheory.CompanionTheory.Mass.MeanV.support_finite (hC : CountBd) (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (T : Finset (HeightOneSpectrum (𝓞 F))) (K : Set (Ainf F))
    (hK : IsCompact K) (Kv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (hKv : ∀ v ∈ T, IsCompact (Kv v))
    (δ : ℝ) (hδ : 0 < δ) :
    {x : F | x ≠ 0 ∧ x ∈ IntOut T ∧ θ δ * algebraMap F (Ainf F) x ∈ K ∧
      ∀ v ∈ T, algebraMap F (Fv F v) x ∈ Kv v}.Finite := by sorry
