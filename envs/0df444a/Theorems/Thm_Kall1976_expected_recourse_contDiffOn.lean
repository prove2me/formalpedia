-- Prove2me | Theorems.Thm_Kall1976_expected_recourse_contDiffOn
-- name    : Kall1976.expected_recourse_contDiffOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T07:13:42.094071+00:00
-- url     : https://prove2.me/theorems/045d93f4-960b-47d1-9e5e-e47345352bcc
-- title:
--   Theorem 12: continuous gradient of expected fixed recourse
-- statement:
--   For fixed recourse, under any of Kall's four moment alternatives, an expected recourse value strictly above negative infinity throughout its almost-sure feasible domain, and an absolutely continuous joint data law, the real expected recourse is finite and integrable on that domain and has a continuous field of within-domain Frechet derivatives there.
-- source:
--   Peter Kall, Stochastic Linear Programming, Springer, 1976, Chapter III section 2, Theorem 12, printed p. 48 / PDF54; Theorem 10 and Corollary 11, printed pp. 46-48 / PDF52-54; fixed W printed p. 45 / PDF51; equations (4)-(5) printed p. 41 / PDF47; expectation equation (8), printed p. 44 / PDF50. https://doi.org/10.1007/978-3-642-66252-2.

import Definitions.Def_Kall1976_RecourseDifferentiability

open MeasureTheory

namespace Kall1976

/-- Kall (1976), III.12, printed48 / PDF54, with III.10/11 alternatives.
The derivative is within the source feasible domain, including its boundary.
A continuous field of linear functionals represents the continuous gradient
in finite coordinates. No complete recourse or interior-only substitution.
The first conjuncts make the reused real expectation faithful on that domain;
they are included consequences of the cited integrability hypotheses. -/
theorem expected_recourse_contDiffOn {m n p : ℕ}
    (μ : Measure (RecourseData m n p)) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin p) ℝ)
    (hmom : recourseMomentAlternative μ)
    (hbelow : ∀ x ∈ recourseDomain μ W, ⊥ < extendedExpectedRecourse μ W x)
    (hdensity : μ ≪ volume) :
    (∀ x ∈ recourseDomain μ W,
      (∀ᵐ d ∂μ, ∃ v : ℝ,
        KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x = (v : EReal)) ∧
      Integrable (fun d =>
        (KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toReal) μ) ∧
    ∃ g : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ),
      ContinuousOn g (recourseDomain μ W) ∧
      ∀ x ∈ recourseDomain μ W,
        HasFDerivWithinAt
          (KallMayer.Recourse.ExpectedRecourse μ W
            (fun d => d.1) (fun d => d.2.1) (fun d => d.2.2))
          (g x) (recourseDomain μ W) x := by sorry

end Kall1976
