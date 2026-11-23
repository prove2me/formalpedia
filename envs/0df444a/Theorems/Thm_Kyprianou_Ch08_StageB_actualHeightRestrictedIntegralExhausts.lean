-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightRestrictedIntegralExhausts
-- name    : Kyprianou.Ch08.StageB.actualHeightRestrictedIntegralExhausts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:56:14.51059+00:00
-- url     : https://prove2.me/theorems/30d48b50-cd89-409a-9b4a-664a7d5b4e5a
-- title:
--   Lemma 8.2: no-drawdown restricted expectation converges to unrestricted expectation
-- statement:
--   For each genuine spectrally negative sample path with finite unit upward passage, its reflected drawdown is bounded up to passage; the no-drawdown restriction therefore exhausts all nonzero discounted integrand mass as the allowed height increases. Use the established original-path unrestricted integrability and measure-theoretic dominated convergence. Preserve the zero convention at infinite passage, source spectral hypotheses and no-drawdown event.
-- source:
--   Kyprianou 2006, Lemma 8.2 p220 / verified original PDF physical p228. Exact two-factor decomposition of the already connected theorem 0ddc9d31-a2da-44ae-9ee4-037e25febe81, preserving the full source model, q range and original path.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightRestrictedIntegralExhausts
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto
      (fun h : ℝ => (∫ ω in
        {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω}, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      atTop (nhds (∫ ω, Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  sorry
