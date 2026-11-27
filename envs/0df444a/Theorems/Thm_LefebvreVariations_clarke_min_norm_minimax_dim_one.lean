-- Prove2me | Theorems.Thm_LefebvreVariations_clarke_min_norm_minimax_dim_one
-- name    : LefebvreVariations.clarke_min_norm_minimax_dim_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:24:52.26381+00:00
-- url     : https://prove2.me/theorems/50508295-e2f7-5d98-b78a-3e197769ac7c
-- title:
--   Lefebvre's variations, No. 269 — on a theme by Burke, Lewis and Overton: the steepest descent identity for the min-norm element of a convex set holds in dimension one
-- statement:
--   Let $G\subseteq\mathbb{R}$ be a nonempty compact convex set, that is, a closed interval $[a,b]$. Then
--   $$
--   -\operatorname{dist}(0,G)\;=\;\min_{|d|\le1}\ \max_{g\in G}\ g\,d ,
--   $$
--   the minimum being attained. Moreover, if $\bar g\in G$ has $|\bar g|=\operatorname{dist}(0,G)$, then the direction $\bar d=-\bar g/|\bar g|$ (taken as $\bar d=0$ when $\bar g=0$) satisfies $|\bar d|\le1$ and
--   $$
--   \max_{g\in G}\ g\,\bar d\;=\;-\operatorname{dist}(0,G).
--   $$
--
--   This is the identity that makes the min-norm element of the convex hull of sampled gradients a steepest-descent direction in the gradient sampling algorithm of Burke, Lewis and Overton for nonsmooth optimization, in dimension $n=1$ where it can be read off the end points of $G$: if $0\in G$ both sides are $0$, if $a>0$ then $\bar g=a$ and $\bar d=-1$, if $b<0$ then $\bar g=b$ and $\bar d=1$.
--
--   **Formalization Note** The ambient space is `EuclideanSpace ℝ (Fin 1)` with the inner product `inner ℝ`; `dist(0 | G)` is `Metric.infDist 0 G`; the minimum over `‖d‖ ≤ 1` of the maximum is stated through `IsLeast` of the set of values `s` for which some `d` of norm at most `1` makes `s` the greatest element of `{⟨g, d⟩ : g ∈ G}`. Here `‖ḡ‖⁻¹ • ḡ` is Lean's inverse, which is `0` for `ḡ = 0`. This is `GradSampling.Conv.lemma_2_1` with `n := 1`; nonemptiness of `G` is assumed as in the parent.
--
--   **Why this is a variation.** This varies the open platform problem GradSampling.Conv.lemma_2_1 (-dist(0|G) = min over unit d of max over g in G of <g,d>, attained at -gbar/|gbar|, for compact convex G in R^n). It is the case n = 1, where G is an interval and the three cases 0 in G, G > 0 and G < 0 can be checked by hand, stated in the parent's own formulation including the convention for gbar = 0.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. V. Burke, A. S. Lewis and M. L. Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005) 751-779, Lemma 2.1 (cited from memory; the lemma number and the page 756 are those quoted on the platform parent and were not checked in the paper). The one-dimensional case was checked by hand on closed intervals [a,b] in the three cases 0 in G, a > 0, b < 0.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **The minimax identity behind gradient sampling, in dimension one.** For a nonempty compact convex
`G ⊆ ℝ¹` (a closed interval), `−dist(0, G) = min_{|d| ≤ 1} max_{g ∈ G} g d`, and if `ḡ ∈ G` has `|ḡ| = dist(0, G)` then
`d̄ = −ḡ/|ḡ|` is a minimizer, with `d̄ = 0` when `ḡ = 0`. This is Lemma 2.1 of Burke, Lewis and Overton, *A robust
gradient sampling algorithm for nonsmooth, nonconvex optimization*, SIAM J. Optim. 15 (2005) 751–779, specialised to
`n = 1`, where it can be read off the endpoints of the interval (cited from memory; page and lemma numbers as in the
platform parent).

**Formalization Note.** Same statement as `GradSampling.Conv.lemma_2_1` at `n = 1`, written with
`EuclideanSpace ℝ (Fin 1)`, `Metric.infDist 0 G` and `inner ℝ`; nonemptiness of `G` is assumed as in the parent. -/
theorem clarke_min_norm_minimax_dim_one (G : Set (EuclideanSpace ℝ (Fin 1))) (hGc : IsCompact G)
    (hGcv : Convex ℝ G) (hGne : G.Nonempty) :
    IsLeast {s : ℝ | ∃ d : EuclideanSpace ℝ (Fin 1), ‖d‖ ≤ 1 ∧
        IsGreatest ((fun g => inner ℝ g d) '' G) s}
        (-Metric.infDist 0 G) ∧
      ∀ gbar ∈ G, ‖gbar‖ = Metric.infDist 0 G →
        ‖-(‖gbar‖⁻¹ • gbar)‖ ≤ 1 ∧
          IsGreatest ((fun g => inner ℝ g (-(‖gbar‖⁻¹ • gbar))) '' G) (-Metric.infDist 0 G) := by
  sorry

end LefebvreVariations
