-- Prove2me | Theorems.Thm_MKVDPP_BStrong_corollary_4_6_B
-- name    : MKVDPP.BStrong.corollary_4_6_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:57.586204+00:00
-- url     : https://prove2.me/theorems/f3d4e170-d939-4335-a425-b013177ac094
-- title:
--   Corollary 4.6 — B strong value over canonical rules
-- statement:
--   Under Assumption 2.8 and for $\nu\in\mathcal P_2(\mathcal C^n)$, the $\mathbb B$ strong value is the supremum of the canonical reward over $\mathbb B$ strong rules:
--
--   $$V_S^{\mathbb B}(t,\nu)=\sup_{\bar P\in\bar{\mathcal P}_S^{\mathbb B}(t,\nu)}J(t,\bar P).$$
--
--   This permits the dynamic programming argument to use canonical laws and conditional continuations.
--
--   **Formalization Note** This is the $\mathbb B$ strong clause; the source also states the ordinary strong clause.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 18, Corollary 4.6, B-strong clause

import Definitions.Def_MKVDPP_BStrong_Canonical

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Corollary 4.6, p. 18, B-strong part of the canonical reward identity. -/
theorem corollary_4_6_B {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    (M : Model T n d ell U) (hA : Assumption28 T n d ell M.u₀ M.b M.σ M.σ₀)
    (Pt : (s : ℝ≥0) → ProbabilityMeasure (Cpath T n) →
      Measure (OmegaT T n d ell s))
    (hPt : ∀ s, ∀ hs : s ≤ T, ∀ μ, IsP2 μ → IsCanonicalLaw s hs μ (Pt s μ))
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n))
    (hν : IsP2 ν) :
    VSB M Pt t ht ν =
      ⨆ P : ProbabilityMeasure (OmegaBar T n d ell),
        ⨆ (_ : P ∈ PbarSB M t ht ν), Jbar M t P := by sorry

end MKVDPP.BStrong
