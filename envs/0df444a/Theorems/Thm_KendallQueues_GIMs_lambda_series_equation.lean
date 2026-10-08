-- Prove2me | Theorems.Thm_KendallQueues_GIMs_lambda_series_equation
-- name    : KendallQueues.GIMs.lambda_series_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:45:05.643631+00:00
-- url     : https://prove2.me/theorems/b63c7d99-4e23-4f72-80ce-24b6ce6378f9
-- title:
--   §7, p. 348 — F(λ) = λ is equivalent to Σ (n | s)λⁿ = λ
-- statement:
--   Let $0<\lambda<1$ and let $(n\mid s)$ be Kendall's service-completion probabilities for a GI/M/s queue. The equation $F(\lambda)=\lambda$ is equivalent to the convergent series equation
--   $$\sum_{n=0}^{\infty}(n\mid s)\lambda^n=\lambda,\qquad F(\lambda)=\int_0^\infty e^{-(1-\lambda)su/b}\,dA(u).$$
--
--   **Formalization Note** Convergence and the sum are expressed together by `HasSum`. The inter-arrival law has finite positive mean $a$ and service has mean $b>0$.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 348, eqs. (16)–(17)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory
open QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- §7, p. 348: the equation `F(λ) = λ` may be written
`∑ (n | s) λ^n = λ`. The series is expressed with `HasSum`. -/
theorem lambda_series_equation (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹)
    (lam : ℝ) (hlam : lam ∈ Set.Ioo (0 : ℝ) 1) :
    F s A b lam = lam ↔
      HasSum (fun n : ℕ => paren A b s n * lam ^ n) lam := by sorry

end KendallQueues.GIMs
