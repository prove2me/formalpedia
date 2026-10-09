-- Prove2me | Theorems.Thm_MKVDPP_BStrong_proposition_2_10
-- name    : MKVDPP.BStrong.proposition_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:25:06.5676+00:00
-- url     : https://prove2.me/theorems/b1b84899-9d54-41bf-9fea-c4c899e84d76
-- title:
--   Proposition 2.10 — B strong fixed space value
-- statement:
--   Under Assumption 2.8, for every $t\in[0,T]$ and $\nu\in\mathcal P_2(\mathcal C^n)$, the intrinsic $\mathbb B$ strong value equals the value over common noise predictable controls on the fixed canonical space:
--
--   $$V_S^{\mathbb B}(t,\nu)=\sup_{\alpha\in\mathcal A_2^{\mathbb B}(t,\nu)}J(t,\nu,\alpha).$$
--
--   The equality transfers the problem to the canonical space used in Theorem 3.2.
--
--   **Formalization Note** This is the $\mathbb B$ strong clause of equation (2.12). It holds for every canonical law family with the prescribed initial and Brownian laws.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 9, Proposition 2.10, equation (2.12), B-strong clause

import Definitions.Def_MKVDPP_BStrong_FixedSpace

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Proposition 2.10, p. 9, B-strong equality in (2.12). -/
theorem proposition_2_10 {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    (M : Model T n d ell U) (hA : Assumption28 T n d ell M.u₀ M.b M.σ M.σ₀)
    (Pt : (s : ℝ≥0) → ProbabilityMeasure (Cpath T n) →
      Measure (OmegaT T n d ell s))
    (hPt : ∀ s, ∀ hs : s ≤ T, ∀ μ, IsP2 μ → IsCanonicalLaw s hs μ (Pt s μ))
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n))
    (hν : IsP2 ν) :
    VSBWeak M t ν = VSB M Pt t ht ν := by sorry

end MKVDPP.BStrong
