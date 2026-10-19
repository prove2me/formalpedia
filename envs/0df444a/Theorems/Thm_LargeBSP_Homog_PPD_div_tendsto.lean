-- Prove2me | Theorems.Thm_LargeBSP_Homog_PPD_div_tendsto
-- name    : LargeBSP.Homog.PPD_div_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:48.493013+00:00
-- url     : https://prove2.me/theorems/e39a7516-129c-42fc-b8cd-e8b49c9d7d5f
-- title:
--   Proof of Theorem 2, p. A2 — (1/N) PPD → V̄(t⋆) − t⋆c
-- statement:
--   Work in the large-offering regime with identical marginal costs: nonnegative valuations with $\mathbb F_{X,N}(y) \Rightarrow F_X(y)$ for $y \ge 0$ (Assumption 1), uniformly integrable with $\frac1N \sum_{n\le N} X_n \Rightarrow \mu$ (Assumption 2), and $c_n = c \ge 0$ for all $n$. Then
--   $$\frac1N\,\mathrm{PPD} = \frac1N \sum_{n=1}^N \mathbb E[(X_n - c)^+] \to \bar V(t^\star) - t^\star c \qquad (N \to \infty),$$
--   where $\bar V(t) = \int_0^t F_X^{-1}(1-s)\,ds$ and $t^\star = \sup\{s \in (0,1) : F_X^{-1}(1-s) \ge c\}$.
--
--   This identifies the linear growth rate of the perfect-price-discrimination benchmark.
--
--   **Formalization Note** PPD is deterministic, so the limit is ordinary convergence.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 2 (Appendix A.1), p. A2, "We are now left to show that (1/N)PPD → V̄(t⋆) − t⋆c"

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- Proof of Theorem 2, p. A2: with identical costs `c ≥ 0`, `(1/N) PPD → V̄(t⋆) − t⋆ c`. -/
theorem PPD_div_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    (hUI : UniformIntegrable X 1 P)
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν))
    (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ => PPD P X (fun _ => c) N / N) atTop
      (𝓝 (Vlim ν (tstar ν c) - tstar ν c * c)) := by sorry

end LargeBSP.Homog
