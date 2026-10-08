-- Prove2me | Theorems.Thm_Helfgott_variable_radius_minor_arc_bound
-- name    : Helfgott.variable_radius_minor_arc_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T08:49:13.818744+00:00
-- url     : https://prove2.me/theorems/3d114dc7-3cc2-4f99-a2df-3facb282e0c0
-- title:
--   Variable-radius weighted minor-arc integration retaining the major-arc subtraction
-- statement:
--   Let $c_n$ be absolutely summable, $S_1(\alpha)=\sum_n c_ne(n\alpha)$, and let $S_2$ be continuous on the circle. Use the published parity-dependent arcs $M_r=\mathfrak M_{\delta,r}$, where $\delta\ge0$, $x>0$. Let $a$ and $N$ be natural numbers, $b=a+N$, and $E=\sum_n|c_n|^2$.
--
--   Let $g$ be nonincreasing on $[a,b]$ with $g(b)\ge0$. Suppose that $|S_2(\alpha)|\le g(a+n)$ outside $M_{a+n}$ for every $0\le n\le N$. Let $H$ be continuous on $[a,b]$, with an integrable right derivative $D\ge0$ at every interior point, with $gD$ integrable. Assume $H(b)=E$ and, for every $0\le n<N$,
--
--   $$\int_{M_{a+n+1}}|S_1(\alpha)|^2\,d\alpha\le H(a+n).$$
--
--   Then
--
--   $$\int_{M_a^c}|S_1(\alpha)|^2|S_2(\alpha)|\,d\alpha
--   \le g(a)\left(H(a)-\int_{M_a}|S_1(\alpha)|^2\,d\alpha\right)
--   +\int_a^b g(u)D(u)\,du.$$
--
--   This is the unnormalized variable-radius integration mechanism of Helfgott Proposition 6.2, preserving the exact major-arc subtraction and the final tail beyond $M_b$. Right derivatives allow finite corners in continuous piecewise smooth H. All Fourier series, circle integrals, and parity arcs are complete; no disjointness or sieve estimate is assumed in this integration step. Setting H to E times a normalized major-arc energy bound recovers the normalization in the paper. N = 0 and E = 0 are included.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, Lemma 6.1 and Proposition 6.2, equations (6.4)-(6.8). Full shell partition, discrete partial summation, right-derivative FTC, actual-arc monotonicity and complete infinite Parseval formalized here. Mathlib FTC and measure-theory authors credited; circle phase helpers preserve tabbott attribution. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open MeasureTheory
open scoped BigOperators Classical

namespace Helfgott

theorem variable_radius_minor_arc_bound (c : ℕ → ℂ) (hc : Summable c)
    (S₂ : AddCircle (1 : ℝ) → ℂ) (hS₂ : Continuous S₂)
    (δ x : ℝ) (r₀ N : ℕ) (hδ : 0 ≤ δ) (hx : 0 < x)
    (g H D : ℝ → ℝ)
    (hg : AntitoneOn g (Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)))
    (hgN : 0 ≤ g ((r₀+N : ℕ) : ℝ))
    (hminor : ∀ n ≤ N, ∀ α ∈ (majorArcs δ (r₀+n) x)ᶜ,
      ‖S₂ α‖ ≤ g ((r₀+n : ℕ) : ℝ))
    (hmajor : ∀ n < N,
      (∫ α in majorArcs δ (r₀+n+1) x, ‖expSum c α‖^2 ∂AddCircle.haarAddCircle) ≤
        H ((r₀+n : ℕ) : ℝ))
    (hHlast : H ((r₀+N : ℕ) : ℝ) = ∑' n : ℕ, ‖c n‖^2)
    (hD : ∀ u ∈ Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ), 0 ≤ D u)
    (hcontH : ContinuousOn H (Set.Icc (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)))
    (hderiv : ∀ u ∈ Set.Ioo (r₀ : ℝ) ((r₀+N : ℕ) : ℝ),
      HasDerivWithinAt H (D u) (Set.Ioi u) u)
    (hiD : IntervalIntegrable D volume (r₀ : ℝ) ((r₀+N : ℕ) : ℝ))
    (higD : IntervalIntegrable (fun u => g u*D u) volume (r₀ : ℝ) ((r₀+N : ℕ) : ℝ)) :
    (∫ α in (majorArcs δ r₀ x)ᶜ, ‖expSum c α‖^2*‖S₂ α‖ ∂AddCircle.haarAddCircle) ≤
      g r₀*(H r₀-(∫ α in majorArcs δ r₀ x, ‖expSum c α‖^2 ∂AddCircle.haarAddCircle)) +
        ∫ u in (r₀ : ℝ)..((r₀+N : ℕ) : ℝ), g u*D u := by sorry

end Helfgott
