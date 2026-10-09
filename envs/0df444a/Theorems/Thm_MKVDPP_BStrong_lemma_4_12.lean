-- Prove2me | Theorems.Thm_MKVDPP_BStrong_lemma_4_12
-- name    : MKVDPP.BStrong.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:25:58.954576+00:00
-- url     : https://prove2.me/theorems/9fd9af7c-9101-4a05-9e13-2dc3489b6ad5
-- title:
--   Lemma 4.12 — analytic strong rule graphs and value
-- statement:
--   The graphs of the Wiener represented rule classes $\bar{\mathcal P}_S^\star$ and $\hat{\mathcal P}_S^\star$ are analytic in their respective time, initial law and canonical law product spaces. Consequently, under Assumption 2.8, the $\mathbb B$ strong value is upper semi analytic:
--
--   $$\{(t,\nu):V_S^{\mathbb B}(t,\nu)>c\}\text{ is analytic for every }c\in\mathbb R.$$
--
--   This is the measurability assertion in Theorem 3.2.
--
--   **Formalization Note** The domain is $[0,T]\times\mathcal P_2(\mathcal C^n)$, with Mathlib's weak topology on laws. On the finite moment subtype, its Borel structure agrees with the Wasserstein topology.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 24, Lemma 4.12

import Definitions.Def_MKVDPP_BStrong_Canonical

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Lemma 4.12, p. 24: both strong-rule graphs are analytic and the B-strong
value is upper semi-analytic on [0,T] × P₂(Cⁿ). -/
theorem lemma_4_12 {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    (M : Model T n d ell U) (hA : Assumption28 T n d ell M.u₀ M.b M.σ M.σ₀)
    (Pt : (s : ℝ≥0) → ProbabilityMeasure (Cpath T n) →
      Measure (OmegaT T n d ell s))
    (hPt : ∀ s, ∀ hs : s ≤ T, ∀ μ, IsP2 μ → IsCanonicalLaw s hs μ (Pt s μ))
    (Pstar : ProbabilityMeasure (Cpath T ell)) (hWiener : IsWiener Pstar) :
    AnalyticSet
      {x : Set.Icc (0 : ℝ≥0) T ×
        {ν : ProbabilityMeasure (Cpath T n) // IsP2 ν} ×
        ProbabilityMeasure (OmegaBar T n d ell) |
        x.2.2 ∈ PbarStarS M Pstar x.1 x.2.1} ∧
    AnalyticSet
      {x : Set.Icc (0 : ℝ≥0) T ×
        {νhat : ProbabilityMeasure (OmegaHat T n d ell) // IsP2 νhat} ×
        ProbabilityMeasure (OmegaBar T n d ell) |
        x.2.2 ∈ PhatStarS M Pstar x.1 x.2.1} ∧
    IsUpperSemianalytic
      (fun x : Set.Icc (0 : ℝ≥0) T ×
        {ν : ProbabilityMeasure (Cpath T n) // IsP2 ν} =>
          VSB M Pt x.1 x.1.property.2 x.2) := by sorry

end MKVDPP.BStrong
