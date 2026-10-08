-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_theorem_30
-- name    : LogBarrierIPM.Iterations.theorem_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:27:48.76993+00:00
-- url     : https://prove2.me/theorems/39e31def-f36d-446c-99f3-4428cac23ffe
-- title:
--   Theorem 30 — every polygonal curve in $\mathcal N^{-\infty}_{\theta,t}$ of $\mathbf{LW}^=_r(t)$ from $\bar\mu\le1$ to $\bar\mu\ge t^2$ has at least $2^{r-1}$ segments
-- statement:
--   Let $r\ge1$ and $0<\theta<1$, and suppose that
--   $$t>\Big(\max\Big((10r-2)!,\ \frac{((10r-1)!)^{24}}{(1-\theta)^3}\Big)\Big)^{2^{r-1}}.\tag{36}$$
--   Let $z^0,z^1,\dots,z^p\in\mathbb R^{2N}$, $N=5r-1$, be the vertices of a polygonal curve $[z^0,z^1]\cup[z^1,z^2]\cup\dots\cup[z^{p-1},z^p]$ contained in the wide neighborhood $\mathcal N^{-\infty}_{\theta,t}$ of the primal-dual central path of $\mathbf{LW}^=_r(t)$, that is, every segment $[z^{i},z^{i+1}]$ lies entirely in $\mathcal N^{-\infty}_{\theta,t}$. If
--   $$\bar\mu(z^0)\le1\qquad\text{and}\qquad\bar\mu(z^p)\ge t^2,$$
--   then the curve contains at least $2^{r-1}$ segments:
--   $$p\ge2^{r-1}.$$
--
--   This is the paper's main result. Any primal-dual path-following interior point method whose iterates and the segments joining them stay in the wide neighborhood, which includes short-step, long-step and predictor-corrector methods, therefore needs at least $2^{r-1}$ iterations to reduce the duality measure from $t^2$ to $1$ on $\mathbf{LW}^=_r(t)$, a linear program with $2r$ variables and $3r+1$ constraints. Such methods are not strongly polynomial.
--
--   **Formalization Note** The curve is a sequence $z:\{0,\dots,p\}\to\mathbb R^{2N}$, and "contained in the neighborhood" is `segment ℝ (z i) (z (i+1)) ⊆ N` for every $i<p$. The power $2^{r-1}$ in (36) is a natural-number power of the real maximum, and $(10r-2)!$, $(10r-1)!$ are natural-number factorials ($10r-2\ge8$ since $r\ge1$). $\bar\mu$ divides by $N=n+m=2r+(3r-1)=5r-1$. The page's labels are kept: $z^0$ is the end with small duality measure.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 27, Theorem 30, eq. (36)

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_SlackLP
import Definitions.Def_LogBarrierIPM_Iterations_LW

namespace LogBarrierIPM.Iterations

/-- Theorem 30 (Allamigeon–Benchimol–Gaubert–Joswig, arXiv:1708.01544v2, p. 27). Let `r ≥ 1`,
`0 < θ < 1` and `t > (max((10r − 2)!, ((10r − 1)!)^24 / (1 − θ)³))^{2^{r−1}}` (36). Every polygonal
curve `[z⁰, z¹] ∪ ⋯ ∪ [z^{p−1}, z^p]` contained in the wide neighborhood `N^{−∞}_{θ,t}` of the
primal-dual central path of `LW^=_r(t)`, with `μ̄(z⁰) ≤ 1` and `μ̄(z^p) ≥ t²`, has `p ≥ 2^{r−1}`
segments. -/
theorem theorem_30 (r : ℕ) (hr : 1 ≤ r) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (t : ℝ)
    (ht : (max (Nat.factorial (10 * r - 2) : ℝ)
      ((Nat.factorial (10 * r - 1) : ℝ) ^ 24 / (1 - θ) ^ 3)) ^ (2 ^ (r - 1)) < t)
    (p : ℕ) (z : Fin (p + 1) → PDPoint (2 * r) (3 * r - 1))
    (hseg : ∀ i : Fin p, segment ℝ (z i.castSucc) (z i.succ) ⊆ lwWideNeighborhood r θ t)
    (hstart : dualityMeasure (z 0) ≤ 1)
    (hend : t ^ 2 ≤ dualityMeasure (z (Fin.last p))) :
    2 ^ (r - 1) ≤ p := by sorry

end LogBarrierIPM.Iterations
