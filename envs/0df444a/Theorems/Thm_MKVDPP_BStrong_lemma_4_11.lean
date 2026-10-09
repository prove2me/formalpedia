-- Prove2me | Theorems.Thm_MKVDPP_BStrong_lemma_4_11
-- name    : MKVDPP.BStrong.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:41.621488+00:00
-- url     : https://prove2.me/theorems/bfcb88b6-468f-490e-9134-47f8031c24c7
-- title:
--   Lemma 4.11 — Wiener represented B strong rules
-- statement:
--   Under Assumption 2.8, the class $\bar{\mathcal P}_S^\star(t,\nu)$ of rules whose common noise and integrated control have a Wiener predictable representation is contained in the $\mathbb B$ strong class and gives the same value:
--
--   $$\bar{\mathcal P}_S^\star(t,\nu)\subseteq\bar{\mathcal P}_S^{\mathbb B}(t,\nu),\qquad V_S^{\mathbb B}(t,\nu)=\sup_{\bar P\in\bar{\mathcal P}_S^\star(t,\nu)}J(t,\bar P).$$
--
--   The restricted class is the object whose graph Lemma 4.12 analyzes.
--
--   **Formalization Note** The unused $\hat\nu$ of the printed statement is omitted. The Wiener law is characterized by the canonical Brownian property.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 23, Lemma 4.11, equation (4.16)

import Definitions.Def_MKVDPP_BStrong_Canonical

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Lemma 4.11, p. 23, including (4.16). -/
theorem lemma_4_11 {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    (M : Model T n d ell U) (hA : Assumption28 T n d ell M.u₀ M.b M.σ M.σ₀)
    (Pt : (s : ℝ≥0) → ProbabilityMeasure (Cpath T n) →
      Measure (OmegaT T n d ell s))
    (hPt : ∀ s, ∀ hs : s ≤ T, ∀ μ, IsP2 μ → IsCanonicalLaw s hs μ (Pt s μ))
    (Pstar : ProbabilityMeasure (Cpath T ell)) (hWiener : IsWiener Pstar)
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n))
    (hν : IsP2 ν) :
    PbarStarS M Pstar t ν ⊆ PbarSB M t ht ν ∧
      VSB M Pt t ht ν =
        ⨆ P : ProbabilityMeasure (OmegaBar T n d ell),
          ⨆ (_ : P ∈ PbarStarS M Pstar t ν), Jbar M t P := by sorry

end MKVDPP.BStrong
