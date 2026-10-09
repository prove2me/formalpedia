-- Prove2me | Theorems.Thm_MKVDPP_BStrong_theorem_3_2
-- name    : MKVDPP.BStrong.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:26:42.191039+00:00
-- url     : https://prove2.me/theorems/d26f3a98-833c-4d3e-8594-0cb9d7e0771d
-- title:
--   Theorem 3.2 — B strong dynamic programming principle
-- statement:
--   Assume Assumption 2.8. The value $V_S^{\mathbb B}$ of common noise adapted strong controls is upper semi analytic on $[0,T]\times\mathcal P_2(\mathcal C^n)$. For an initial pair $(t,\nu)$ and a stopping time $\tau$ of the raw common noise filtration on the fixed canonical space, taking values in $[t,T]$, it obeys
--
--   $$V_S^{\mathbb B}(t,\nu)=\sup_{\alpha\in\mathcal A_2^{\mathbb B}(t,\nu)}\mathbb E\!\left[\int_t^\tau L(s,X^\alpha_{s\wedge\cdot},\bar\mu_s^\alpha,\alpha_s)\,ds+V_S^{\mathbb B}(\tau,\mu_\tau^\alpha)\right].$$
--
--   This is the paper's dynamic programming principle for common noise adapted strong control.
--
--   **Formalization Note** The fixed law is any family with the prescribed initial law and independent Brownian increments. The supremum includes every strong solution and conditional law version, with uniqueness supplied by Theorem A.3(i). The stopped conditional law uses the stopped augmented common noise sigma algebra. Expectations use $\infty-\infty=-\infty$.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 10, Theorem 3.2, equation (3.3)

import Definitions.Def_MKVDPP_BStrong_Canonical

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Theorem 3.2, p. 10: upper semi-analyticity and the DPP (3.3) for the
common-noise-adapted strong formulation. -/
theorem theorem_3_2 {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U]
    (M : Model T n d ell U) (hA : Assumption28 T n d ell M.u₀ M.b M.σ M.σ₀)
    (Pt : (s : ℝ≥0) → ProbabilityMeasure (Cpath T n) →
      Measure (OmegaT T n d ell s))
    (hPt : ∀ s, ∀ hs : s ≤ T, ∀ μ, IsP2 μ → IsCanonicalLaw s hs μ (Pt s μ)) :
    IsUpperSemianalytic
      (fun x : Set.Icc (0 : ℝ≥0) T ×
        {ν : ProbabilityMeasure (Cpath T n) // IsP2 ν} =>
          VSB M Pt x.1 x.1.property.2 x.2) ∧
    ∀ (t : ℝ≥0) (ht : t ≤ T) (ν : ProbabilityMeasure (Cpath T n))
      (hν : IsP2 ν) (τ : OmegaT T n d ell t → ℝ≥0),
      (hτstop : IsStoppingFor (rawGt t ht) τ) →
      (hτ : ∀ ω, t ≤ τ ω ∧ τ ω ≤ T) →
      VSB M Pt t ht ν =
        ⨆ (α : ℝ≥0 → OmegaT T n d ell t → U),
          ⨆ (_ : α ∈ AB2 M Pt t ht ν),
            ⨆ (X : OmegaT T n d ell t → Cpath T n),
              ⨆ (μbar : ℝ≥0 → OmegaT T n d ell t →
                ProbabilityMeasure (Cpath T n × U)),
                ⨆ (_ : IsFixedSolution M Pt t ht ν α X μbar),
                  ⨆ (mτ : OmegaT T n d ell t → ProbabilityMeasure (Cpath T n)),
                    ⨆ (_ : IsCondLaw (stoppedSigma (Gt t ht (Pt t ν)) τ)
                      (Pt t ν) (fun ω => stopPath (τ ω) (X ω)) mτ),
                      eExp (Pt t ν) (fun ω =>
                        timeInt t (τ ω) (fun s =>
                          (M.L s (stopPath s (X ω)) (μbar s ω) (α s ω) : EReal)) +
                        VSB M Pt (τ ω) (hτ ω).2
                          (mτ ω)) := by sorry

end MKVDPP.BStrong
