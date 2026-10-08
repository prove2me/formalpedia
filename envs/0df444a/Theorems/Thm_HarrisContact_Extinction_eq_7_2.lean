-- Prove2me | Theorems.Thm_HarrisContact_Extinction_eq_7_2
-- name    : HarrisContact.Extinction.eq_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:56:14.541777+00:00
-- url     : https://prove2.me/theorems/e1966829-0558-4d36-8a6c-30403459b109
-- title:
--   (7.2), p. 981 — for μ = 1, λ_k = kλ: π₁ = 2dλ/(1 + 2dλ) · π₂
-- statement:
--   Consider the contact process on $Z_d$ ($d\ge1$) with $\mu=1$ and $\lambda_k=k\lambda$, $\lambda\ge0$. Write $\pi_1=p_\infty(\{x\})$ and $\pi_2=p_\infty(\{x,y\})$ for a pair of neighbours. Then for every site $x$ and every neighbour $y$ of $x$,
--   $$\pi_1=\frac{2d\lambda}{1+2d\lambda}\,\pi_2 .$$
--
--   From a single infected site the first jump is a recovery with probability $1/(1+2d\lambda)$ and an infection of one of the $2d$ neighbours otherwise; the identity is the resulting first-step equation. It is the first of the two relations from which Theorem 7.1 is derived.
--
--   **Formalization Note** The statement quantifies over every site and every neighbour, so it includes the fact, implicit on the page, that $\pi_1$ and $\pi_2$ do not depend on the chosen site or pair. The ratio is a nonnegative real embedded in $[0,\infty]$.
-- source:
--   Harris (Ann. Probab. 2, 1974), §7, proof of Theorem 7.1, (7.2), p. 981

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.Extinction

/-- (7.2) (p. 981): with μ = 1 and λ_k = kλ, π₁ = 2dλ/(1 + 2dλ) · π₂ for every site x and
every neighbour y of x. -/
theorem eq_7_2 {d : ℕ} (hd : 1 ≤ d) (l : ℝ) (hl : 0 ≤ l) :
    ∀ x y : Site d, ∑ i, |x i - y i| = 1 →
      survInf 1 (fun k => (k : ℝ) * l) {x} =
        ENNReal.ofReal (2 * d * l / (1 + 2 * d * l)) * survInf 1 (fun k => (k : ℝ) * l) {x, y} := by sorry

end HarrisContact.Extinction
