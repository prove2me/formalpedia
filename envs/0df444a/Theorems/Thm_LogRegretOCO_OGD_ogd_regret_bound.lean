-- Prove2me | Theorems.Thm_LogRegretOCO_OGD_ogd_regret_bound
-- name    : LogRegretOCO.OGD.ogd_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:33:45.843985+00:00
-- url     : https://prove2.me/theorems/54023a11-4050-4c43-9292-c6f37eab5e43
-- title:
--   Theorem 1 — Online Gradient Descent with step sizes 1/(Ht) has regret ≤ (G²/2H)(1 + log T)
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^n$ be nonempty, closed, bounded and convex. Let $H>0$ and $G\in\mathbb R$, fix a horizon $T\ge1$, and let $f_1,\dots,f_T:\mathbb R^n\to\mathbb R$ be cost functions such that, for every round $t\in\{1,\dots,T\}$,
--
--   1. $f_t$ is $H$-strongly convex on $\mathcal P$: twice differentiable at the points of $\mathcal P$ with $\nabla^2 f_t(x)\succeq H I_n$ for every $x\in\mathcal P$;
--   2. $\|\nabla f_t(x)\|_2\le G$ for every $x\in\mathcal P$.
--
--   Let $x_1,x_2,\dots$ be a run of ONLINE GRADIENT DESCENT (Fig. 1) on $\mathcal P$ with step sizes $\eta_{t+1}=\frac1{Ht}$ for $t\ge1$: $x_1\in\mathcal P$ is arbitrary and $x_{t+1}=\Pi_{\mathcal P}\bigl(x_t-\tfrac{1}{Ht}\nabla f_t(x_t)\bigr)$. Then for every $u\in\mathcal P$,
--   $$\sum_{t=1}^{T}\bigl(f_t(x_t)-f_t(u)\bigr)\ \le\ \frac{G^2}{2H}\,\bigl(1+\log T\bigr).$$
--
--   Since this holds for every $u\in\mathcal P$, it bounds the regret $\sum_t f_t(x_t)-\min_{x\in\mathcal P}\sum_t f_t(x)$ of the algorithm; and since the cost functions are arbitrary (each $x_t$ depends only on $f_1,\dots,f_{t-1}$), it is the worst-case bound $\mathrm{Regret}_T(\mathrm{OGD})\le\frac{G^2}{2H}(1+\log T)$ of the paper. It is the first of the paper's logarithmic regret bounds, improving Zinkevich's $O(GD\sqrt T)$ for general convex costs.
--
--   **Formalization Note** The theorem states "step sizes $\eta_t=\frac1{Ht}$"; its proof takes the step after round $t$ to be $\eta_{t+1}=\frac1{Ht}$, and that indexing is used here. Fig. 1 read literally with $\eta_t=\frac1{Ht}$ steps by $\frac1{H(t+1)}$ after round $t$, which leaves an extra $\frac H2\|x_1-x^*\|^2$ in the bound. Regret is stated against every comparator $u\in\mathcal P$ (the minimum over the compact $\mathcal P$ is attained), never as a real infimum. The hypotheses on $f_t$ are required for $t\in\{1,\dots,T\}$ only; the run is a predicate on the whole trajectory. The paper's standing assumption that the $f_t$ are convex follows from $H$-strong convexity on the convex set $\mathcal P$ and is not added. Boundedness and closedness of $\mathcal P$ are the standing assumptions of §2.1 (closedness also makes the projection exist); no diameter bound is used. $\log$ is the natural logarithm, and at $T=1$ the bound is $G^2/(2H)$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 175, Theorem 1 (algorithm: p. 174, Fig. 1; setting: pp. 171–172, §2.1–2.2)

import Mathlib
import Definitions.Def_LogRegretOCO_OGD_Model

namespace LogRegretOCO.OGD

/-- **Theorem 1** (p. 175): ONLINE GRADIENT DESCENT with step sizes `1/(Ht)` (the step taken
after round `t`, i.e. `η_{t+1} = 1/(Ht)` as in the proof) on `H`-strongly convex costs whose
gradients are bounded by `G` on `P` has, for every `T ≥ 1` and every comparator `u ∈ P`,
`∑_{t=1}^T (f_t(x_t) − f_t(u)) ≤ G²/(2H) · (1 + log T)`. -/
theorem ogd_regret_bound {n : ℕ} (P : Set (E n)) (hPc : Convex ℝ P) (hPcl : IsClosed P)
    (hPb : Bornology.IsBounded P) (hPne : P.Nonempty) (H G : ℝ) (hH : 0 < H) (T : ℕ)
    (hT : 1 ≤ T) (f : ℕ → E n → ℝ)
    (hsc : ∀ t ∈ Finset.Icc 1 T, IsHStrongConvex P H (f t))
    (hG : ∀ t ∈ Finset.Icc 1 T, ∀ x ∈ P, ‖gradient (f t) x‖ ≤ G)
    (η : ℕ → ℝ) (hη : ∀ t : ℕ, 1 ≤ t → η (t + 1) = 1 / (H * (t : ℝ)))
    (x : ℕ → E n) (hx : IsOGDRun P η f x) (u : E n) (hu : u ∈ P) :
    ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t u) ≤ G ^ 2 / (2 * H) * (1 + Real.log T) := by sorry

end LogRegretOCO.OGD
