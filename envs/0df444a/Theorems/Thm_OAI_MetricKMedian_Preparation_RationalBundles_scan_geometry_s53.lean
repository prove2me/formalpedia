-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_RationalBundles_scan_geometry_s53
-- name    : OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:45:35.213769+00:00
-- url     : https://prove2.me/theorems/8d462ac1-a168-4f23-8926-cbb374540c4c
-- title:
--   OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry` of [lean/OAI/Combinatorics/KMedian/Geometry/RationalGeometryScan.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/RationalGeometryScan.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation.RationalBundles`, with `open Finset SupplierStars RationalSuppliers`):
--
--   ```lean
--    theorem scan_geometry_s53 {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
--       (heven : Even qR.Δ) (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j)
--       (F : Fin n → Finset (Fin f)) (Fj : Fin j → Finset (Fin f)) (y : Fin f → ℚ)
--       (s : Fin n → X) (i : Fin f → X) (client : Fin j → X)
--       (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
--       (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
--       (V : Fin n → ℚ) (v : Fin j → ℚ) (rep : Fin j → Fin n) (M δ γ T₁ B : ℚ)
--       (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
--       (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
--       (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
--       (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
--       (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a≤1)
--       (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) ≤ 1/4)
--       (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1) (hT : 0<T₁)
--       (hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ)) ≤ 1/4)
--       (hfail : failureFactor (γ:ℝ) (qR.g:ℝ)<1)
--       (hB : (∑ a, (y a:ℝ))+3*(qR.g:ℝ)+(qR.allowance:ℝ) ≤ (B:ℝ))
--       (hu : ∀ t, ∑ a ∈ F t, y a=1)
--       (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
--       (hju : ∀ c, ∑ a ∈ Fj c, y a=1)
--       (hjv : ∀ c, ∑ a ∈ Fj c, y a*dc c a=v c)
--       (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u)
--       (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, di t a≤di t b)
--       (hrepV : ∀ c, V (rep c)≤v c) (hrepD : ∀ c, dist (client c) (s (rep c))≤(M:ℝ)*(v c:ℝ)) :
--       let D := suppliers F y s i d di V M δ γ hd hdi hy hM hδ (by linarith only [hδ1]) hθ hγ hγ1 hu hv hs;
--       ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
--         (O.card:ℝ)≤(B:ℝ) ∧ (Completion.Rational.score dc O:ℝ) ≤
--         ((1+2/Real.exp 1+τ)/(1-τ)) *
--         (max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
--           (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (qR.g:ℝ)) /
--           (1-failureFactor (γ:ℝ) (qR.g:ℝ)))*(∑ c, (v c:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.Preparation.failureFactor` and `OAI.MetricKMedian.Preparation.farFactor` (definitions bundle `OAIQ053K003` of this split); `OAI.MetricKMedian.Preparation.nearFactor` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.Preparation.RationalSuppliers.Data` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` and `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.Preparation.RationalBundles.suppliers` (definitions bundle `OAIQ053K040` of this split); `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan` (definitions bundle `OAIQ053K049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Instance.computedPseudo_spec_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Geometry/RationalGeometryScan.lean (declaration OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry)

import Mathlib
import Definitions.Def_OAIQ053K049

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Preparation.RationalBundles
open Finset SupplierStars RationalSuppliers
variable {f n j : ℕ} {X : Type} [PseudoMetricSpace X]

 theorem scan_geometry_s53 {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
    (heven : Even qR.Δ) (hτ0 : 0<τ) (hτ : τ<1) (hj : 0<j)
    (F : Fin n → Finset (Fin f)) (Fj : Fin j → Finset (Fin f)) (y : Fin f → ℚ)
    (s : Fin n → X) (i : Fin f → X) (client : Fin j → X)
    (d : Fin n → Fin n → ℚ) (di : Fin n → Fin f → ℚ)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (V : Fin n → ℚ) (v : Fin j → ℚ) (rep : Fin j → Fin n) (M δ γ T₁ B : ℚ)
    (hd : ∀ t u, dist (s t) (s u)=(d t u:ℝ))
    (hdi : ∀ t a, dist (s t) (i a)=(di t a:ℝ))
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a≤1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : (δ:ℝ) ≤ 1/4)
    (hθ : 1/((M:ℝ)*(δ:ℝ)) ≤ 1/8) (hγ : 0<γ) (hγ1 : γ≤1) (hT : 0<T₁)
    (hα : (M:ℝ)/((δ:ℝ)*(T₁:ℝ)) ≤ 1/4)
    (hfail : failureFactor (γ:ℝ) (qR.g:ℝ)<1)
    (hB : (∑ a, (y a:ℝ))+3*(qR.g:ℝ)+(qR.allowance:ℝ) ≤ (B:ℝ))
    (hu : ∀ t, ∑ a ∈ F t, y a=1)
    (hv : ∀ t, ∑ a ∈ F t, y a*di t a=V t)
    (hju : ∀ c, ∑ a ∈ Fj c, y a=1)
    (hjv : ∀ c, ∑ a ∈ Fj c, y a*dc c a=v c)
    (hs : ∀ t u, t ≠ u → M*max (V t) (V u) < d t u)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, di t a≤di t b)
    (hrepV : ∀ c, V (rep c)≤v c) (hrepD : ∀ c, dist (client c) (s (rep c))≤(M:ℝ)*(v c:ℝ)) :
    let D := suppliers F y s i d di V M δ γ hd hdi hy hM hδ (by linarith only [hδ1]) hθ hγ hγ1 hu hv hs;
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ)≤(B:ℝ) ∧ (Completion.Rational.score dc O:ℝ) ≤
      ((1+2/Real.exp 1+τ)/(1-τ)) *
      (max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
        (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) (qR.g:ℝ)) /
        (1-failureFactor (γ:ℝ) (qR.g:ℝ)))*(∑ c, (v c:ℝ)) := by
  sorry

end MetricKMedian.Preparation.RationalBundles
end

end OAI
end
