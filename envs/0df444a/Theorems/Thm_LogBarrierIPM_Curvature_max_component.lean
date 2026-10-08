-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_max_component
-- name    : LogBarrierIPM.Curvature.max_component
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:23:00.66771+00:00
-- url     : https://prove2.me/theorems/a75615ea-66c4-42d0-b163-d72016177e38
-- title:
--   Proof of Theorem 25 — the maximal component of $\mathcal C^{\mathrm{trop}}(4k/2^{r-1})$ is $r-1+(2k+2)/2^{r-1}$, uniquely attained by $w_{3(r-1)}$ or $w_{3(r-1)+1}$
-- statement:
--   Let $r\ge2$, let $0\le k\le 2^{r-2}$, and let $\lambda_k=\frac{4k}{2^{r-1}}$. Let $\mathcal C^{\mathrm{trop}}(\lambda_k)=(x,w,s,y)\in\mathbb R^{2N}$ be the point of the tropical central path of $\mathbf{LW}_r$, and set
--   $$M_k=r-1+\frac{2k+2}{2^{r-1}},\qquad i^*=\begin{cases}3(r-1)&k\text{ odd},\\ 3(r-1)+1&k\text{ even}.\end{cases}$$
--   Then
--
--   1. the maximal component of $\mathcal C^{\mathrm{trop}}(\lambda_k)$ over all its $2N$ coordinates $x_j,w_i,s_j,y_i$ equals $M_k$, and $w_{i^*}=M_k$;
--   2. unless $r=2$ and $k=0$, this maximum is attained only by $w_{i^*}$: every other coordinate is strictly less than $M_k$.
--
--   This locates the leading coordinate of the tropical central path at the subdivision points $\lambda_k$ of $[0,2]$, and its alternation between $w_{3(r-1)}$ and $w_{3(r-1)+1}$ is what produces a right tropical angle at each interior subdivision point.
--
--   **Formalization Note** The paper asserts unique attainment for every $k$. At $r=2$, $k=0$ ($\lambda=0$) it fails: $w_1=2=w_4=M_0$. That point is not used by the proof (for $r=2$ there is no interior subdivision point), so uniqueness is stated with the exclusion $(r,k)\ne(2,0)$, and the value of the maximum is stated for all $k$. Coordinates use the paper's 1-based indices.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 23, proof of Theorem 25, third paragraph (unnumbered claim; subdivision λ_k = 4k/2^{r−1}, first paragraph)

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TropicalCentralPathLW

namespace LogBarrierIPM.Curvature

/-- Proof of Theorem 25, maximal-component claim (p. 23). Let `r ≥ 2`, `0 ≤ k ≤ 2^{r−2}` and
`λ_k = 4k/2^{r−1}`. The maximal component of `C^trop(λ_k) = (x, w, s, y)` (for `LW_r`) equals
`M = r − 1 + (2k+2)/2^{r−1}` and is attained by `w_{i*}`, `i* = 3(r−1)` for odd `k` and
`i* = 3(r−1)+1` for even `k`; unless `(r, k) = (2, 0)`, every other coordinate is `< M`. -/
theorem max_component (r k : ℕ) (hr : 2 ≤ r) (hk : k ≤ 2 ^ (r - 2)) :
    let lam : ℝ := 4 * (k : ℝ) / 2 ^ (r - 1)
    let M : ℝ := ((r : ℝ) - 1) + (2 * (k : ℝ) + 2) / 2 ^ (r - 1)
    let istar : ℕ := if Odd k then 3 * (r - 1) else 3 * (r - 1) + 1
    tropW lam istar = M ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 2 * r → tropX lam i ≤ M ∧ tropS lam i ≤ M) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 3 * r - 1 → tropW lam i ≤ M ∧ tropY lam i ≤ M) ∧
    (¬ (r = 2 ∧ k = 0) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 2 * r → tropX lam i < M ∧ tropS lam i < M) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 3 * r - 1 → i ≠ istar → tropW lam i < M) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ 3 * r - 1 → tropY lam i < M)) := by sorry

end LogBarrierIPM.Curvature
