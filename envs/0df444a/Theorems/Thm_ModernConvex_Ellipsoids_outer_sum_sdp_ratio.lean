-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_outer_sum_sdp_ratio
-- name    : ModernConvex.Ellipsoids.outer_sum_sdp_ratio
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:57.567097+00:00
-- url     : https://prove2.me/theorems/c577cacc-6d86-4978-8059-74ad1834109c
-- title:
--   Proposition 4.9.5 — the (Õ) ellipsoid has volume within (π/2)^{n/2} of the smallest ellipsoid containing W₁ + ⋯ + W_m
-- statement:
--   Let $W_i=\{x\in\mathbb R^n \mid x^TB_ix\le1\}$ with $B_i\succ0$, $i=1,\dots,m$, be full-dimensional ellipsoids centred at the origin, and let $W=W_1+\dots+W_m$ be their arithmetic sum. Let $B^i$ be the $(mn)\times(mn)$ block-diagonal matrix with $i$-th diagonal block $B_i$ and all other blocks zero, and $M[Z]$ the $(mn)\times(mn)$ matrix of $m^2$ blocks all equal to $Z$. Let $(t_*,Z_*,\lambda_*)$ be an optimal solution of
--   $$\max_{t,Z,\lambda}\Big\{t \;\Big|\; t\le\operatorname{Det}^{1/n}(Z),\ \sum_{i=1}^m\lambda_iB^i\succeq M[Z],\ \lambda_i\ge0,\ Z\succeq0,\ \sum_{i=1}^m\lambda_i=1\Big\}.\qquad(\tilde O)$$
--   Let $W[Z_{**}]=\{x \mid x^TZ_{**}x\le1\}$, $Z_{**}\succ0$, be the true smallest-volume ellipsoid containing $W$: it contains $W$, and no full-dimensional ellipsoid containing $W$ (with any centre) has smaller volume. Then the ratio $\vartheta=\operatorname{Vol}(W[Z_*])/\operatorname{Vol}(W[Z_{**}])$ satisfies $\vartheta\le(\pi/2)^{n/2}$, that is,
--   $$\operatorname{Vol}(W[Z_*])\le\Big(\frac{\pi}{2}\Big)^{n/2}\operatorname{Vol}(W[Z_{**}]).$$
--
--   The ellipsoid $W[Z_*]$ is computable by semidefinite programming and contains $W$ (Proposition 4.9.4). The bound says it is within a factor $\sqrt{\pi/2}\approx1.253$ of optimal in average linear size.
--
--   **Formalization Note** Volume is normalized (Lebesgue measure divided by that of the unit Euclidean ball, valued in $[0,\infty]$). The book's ratio $\vartheta$ is stated in product form, with $(\pi/2)^{n/2}$ a real power embedded as a nonnegative extended real. $W[Z_{**}]$ is given by hypotheses: $Z_{**}\succ0$, $W\subseteq W[Z_{**}]$, and $\operatorname{Vol}(W[Z_{**}])\le\operatorname{Vol}(E)$ for every full-dimensional ellipsoid $E\supseteq W$. Such a $Z_{**}$ exists by the Fritz John theorem (Theorem 4.9.1(ii)) and the central symmetry of $W$ (p. 269), so the hypotheses are satisfiable. An optimal solution of $(\tilde O)$ exists by compactness when $m\ge1$. For $m=0$ the program is infeasible and the statement is vacuous; the book does not consider $m=0$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 268, Proposition 4.9.5

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, Proposition 4.9.5, p. 268. Let `Wᵢ = {x | xᵀBᵢx ≤ 1}`, `Bᵢ ≻ 0`,
`i = 1, …, m`, and `W = W₁ + ⋯ + W_m`. Let `W[Z∗] = {x | xᵀZ∗x ≤ 1}` be given by an optimal
solution `(t∗, Z∗, λ∗)` of (Õ), and let `W[Z∗∗] = {x | xᵀZ∗∗x ≤ 1}`, `Z∗∗ ≻ 0`, be the true
smallest-volume ellipsoid containing `W` (no full-dimensional ellipsoid containing `W` has smaller
volume). Then `ϑ = Vol(W[Z∗]) / Vol(W[Z∗∗]) ≤ (π/2)^{n/2}`, stated in product form. -/
theorem outer_sum_sdp_ratio {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosDef)
    (Zss : Matrix (Fin n) (Fin n) ℝ) (hZss : Zss.PosDef)
    (hcont : minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Zss)
    (hmin : ∀ E : Set (Fin n → ℝ), IsFullDimEllipsoid E →
      minkowskiSum (fun i => quadSet (B i)) ⊆ E → Vol (quadSet Zss) ≤ Vol E)
    (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ) (hopt : OOptimal B t Z lam) :
    Vol (quadSet Z) ≤
      ENNReal.ofReal ((Real.pi / 2) ^ ((n : ℝ) / 2)) * Vol (quadSet Zss) := by sorry

end ModernConvex.Ellipsoids
