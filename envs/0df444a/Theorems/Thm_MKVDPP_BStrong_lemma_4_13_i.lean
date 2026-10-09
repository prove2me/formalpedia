-- Prove2me | Theorems.Thm_MKVDPP_BStrong_lemma_4_13_i
-- name    : MKVDPP.BStrong.lemma_4_13_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:27.188115+00:00
-- url     : https://prove2.me/theorems/1b4457fb-84c3-49b8-b76c-a041fdfdf787
-- title:
--   Lemma 4.13(i) — conditioning preserves B strong rules
-- statement:
--   Let $\bar P$ be a $\mathbb B$ strong canonical rule from $(t,\nu)$ and let $\bar\tau\in[t,T]$ be a common noise stopping time. If $\kappa_{\bar\omega}$ is a regular conditional probability distribution given the stopped common noise sigma algebra, then for almost every sample point its continuation remains a $\mathbb B$ strong rule from the stopped conditional state law:
--
--   $$\kappa_{\bar\omega}\in\bar{\mathcal P}_S^{\mathbb B}\!\left(\bar\tau(\bar\omega),\mu_{\bar\tau(\bar\omega)}(\bar\omega)\right)\quad\bar P\text{-a.s.}$$
--
--   This supplies the conditioning step for the dynamic programming inequality.
--
--   **Formalization Note** The conclusion includes a finite second moment for the stopped law. The regular conditional distribution retains the pointwise atom condition.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 25, Lemma 4.13(i)

import Definitions.Def_MKVDPP_BStrong_Canonical

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Lemma 4.13(i), p. 25: a regular conditional continuation of a B-strong
control rule is again B-strong at its stopped conditional state law. -/
theorem lemma_4_13_i {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    (M : Model T n d ell U)
    (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n))
    (hν : IsP2 ν) (P : ProbabilityMeasure (OmegaBar T n d ell))
    (hP : P ∈ PbarSB M t ht ν)
    (τ : OmegaBar T n d ell → ℝ≥0)
    (hτstop : IsStoppingFor (rawGbar t) τ)
    (hτ : ∀ ω, t ≤ τ ω ∧ τ ω ≤ T)
    (κ : OmegaBar T n d ell → ProbabilityMeasure (OmegaBar T n d ell))
    (hκ : IsRCPD (stoppedSigma (rawGbar t) τ) P.toMeasure κ) :
    ∀ᵐ ω ∂P.toMeasure,
      IsP2 (barMu (τ ω) ω) ∧
        κ ω ∈ PbarSB M (τ ω) (hτ ω).2 (barMu (τ ω) ω) := by sorry

end MKVDPP.BStrong
