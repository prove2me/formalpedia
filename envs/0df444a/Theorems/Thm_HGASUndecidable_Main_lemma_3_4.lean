-- Prove2me | Theorems.Thm_HGASUndecidable_Main_lemma_3_4
-- name    : HGASUndecidable.Main.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:14:32.042376+00:00
-- url     : https://prove2.me/theorems/6e91279c-d34e-4656-8e3f-b51ba9aa42d2
-- title:
--   Lemma 3.4 — β(Φ, a) = lim M(T)/T = inf M(T)/T; β < 0 iff a uniform negative finite-time integral
-- statement:
--   Let K be a nonempty compact metric space with its Borel σ-algebra, Φ a continuous flow for all real times, and a a continuous real function. Let M(T) be the maximum over initial states of the integral of a along the flow from 0 to T, and β the maximum invariant probability average. Lemma 3.4. Let a ∈ C(K) and M(T) = max_{x∈K} ∫_0^T a(Φ^t x) dt for T > 0. Then β(Φ, a) = lim_{T→∞} M(T)/T = inf_{T>0} M(T)/T. (3.4) In particular, β(Φ, a) < 0 if and only if there are T, c > 0 such that ∫_0^T a(Φ^t x) dt ≤ −c for every x ∈ K. (3.5)
--
--   Differences from the source:
--   - encoding: the maximum invariant average and maximum finite-time orbit integral → real suprema over invariant Borel probability measures and initial states, respectively; reason: compactness, continuity and nonemptiness in the source guarantee attainment and boundedness; no maximization is over arbitrary noninvariant measures
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Lemma 3.4, printed p. 18 (PDF 20)

import Definitions.Def_HGASUndecidable_Main_Dynamics

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem lemma_3_4 {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
    [MeasurableSpace K] [BorelSpace K] (Φ : Flow ℝ K) (a : K → ℝ) (ha : Continuous a) :
    Tendsto (fun T : ℝ => maxIntegral Φ a T / T) atTop (𝓝 (beta Φ a)) ∧
    beta Φ a = sInf {v | ∃ T : ℝ, 0 < T ∧ v = maxIntegral Φ a T / T} ∧
    (beta Φ a < 0 ↔ ∃ T c : ℝ, 0 < T ∧ 0 < c ∧ ∀ x, orbitIntegral Φ a x T ≤ -c) := by sorry

end HGASUndecidable.Main
