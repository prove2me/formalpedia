-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightUnrestrictedUpcrossingNormalisation
-- name    : Kyprianou.Ch08.StageB.actualHeightUnrestrictedUpcrossingNormalisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:56:14.848192+00:00
-- url     : https://prove2.me/theorems/0cde6f5b-ab0b-4d17-acf2-e7111fd93b8f
-- title:
--   Lemma 8.2: unrestricted discounted original unit upcrossing has Esscher normalisation one
-- statement:
--   For the actual spectrally negative model and every nonnegative discount q, the unrestricted original-path unit upward first-passage discount has exact Esscher normalisation one, with the discounted payoff at infinite passage explicitly zero. The currently proved unrestricted bound is only an upper estimate; equality requires a genuine lower bound or first-passage transform and retains the q=0 case.
-- source:
--   Kyprianou 2006, Lemma 8.2 p220 / verified original PDF physical p228. Exact two-factor decomposition of the already connected theorem 0ddc9d31-a2da-44ae-9ee4-037e25febe81, preserving the full source model, q range and original path.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightUnrestrictedUpcrossingNormalisation
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ ω, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P) = 1 := by
  sorry
