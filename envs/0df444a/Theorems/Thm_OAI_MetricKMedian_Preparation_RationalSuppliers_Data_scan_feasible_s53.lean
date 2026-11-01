-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_RationalSuppliers_Data_scan_feasible_s53
-- name    : OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:47:56.141991+00:00
-- url     : https://prove2.me/theorems/98fb3522-ba22-4b76-ab63-0205aba138f7
-- title:
--   OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible` of [lean/OAI/Combinatorics/KMedian/Preparation/RationalSupplierScan.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Preparation/RationalSupplierScan.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation.RationalSuppliers.Data`, with `open Finset SupplierStars`):
--
--   ```lean
--   theorem scan_feasible_s53 {X : Type} [PseudoMetricSpace X]
--       (heven : Even qR.Δ) (hτ : τ<1) (hj : 0<j)
--       (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
--       (i : Fin f → X) (client : Fin j → X)
--       (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
--       (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
--       (B : ℚ) (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
--       (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z)
--       (hcap : ∀ a, physicalCount (D.coupled qR heven) z a ≤ qR.Δ)
--       (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))
--       (hB : (∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
--       (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
--       (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ)) ∧
--         (∑ a, r c a)=1) :
--       ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
--         (O.card:ℝ) ≤ (B:ℝ) ∧
--         (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
--           (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.FiniteLaw` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.Preparation.Physical`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Data`, `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.targets` and `OAI.MetricKMedian.Preparation.SupplierStars.weight` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` and `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.FiniteLaw.joint` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.flag` (definitions bundle `OAIQ053K026` of this split); `OAI.MetricKMedian.Preparation.physicalCount` and `OAI.MetricKMedian.Preparation.CoupledLaw` (definitions bundle `OAIQ053K036` of this split); `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan` (definitions bundle `OAIQ053K049` of this split); `OAI.MetricKMedian.Preparation.RationalSuppliers.Data.coupled` (definitions bundle `OAIQ053K078` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.RationalBundles.scan_geometry_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Preparation/RationalSupplierScan.lean (declaration OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_feasible)

import Mathlib
import Definitions.Def_OAIQ053K078

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

theorem scan_feasible_s53 {X : Type} [PseudoMetricSpace X]
    (heven : Even qR.Δ) (hτ : τ<1) (hj : 0<j)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (B : ℚ) (z : (D.coupled qR heven).Ω × (Fin n → Finset (Fin f)))
    (hz : 0 < ((D.coupled qR heven).ν.joint (D.coupled qR heven).κ).weight z)
    (hcap : ∀ a, physicalCount (D.coupled qR heven) z a ≤ qR.Δ)
    (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))
    (hB : (∑ a, (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
    (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(physicalCount (D.coupled qR heven) z a:ℝ)) ∧
      (∑ a, r c a)=1) :
    ∃ O : Finset (Fin f), D.scan qR df dc B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
        (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  sorry

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end
