-- Prove2me | Theorems.Thm_IncProx_Randomized_eq59
-- name    : IncProx.Randomized.eq59
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:31.936196+00:00
-- url     : https://prove2.me/theorems/fc79f74d-30f8-4051-ae57-2c0ac45db7ed
-- title:
--   Eq. (59) — for each $x^*\in X^*$, a.s. $\sum_k\frac{2\alpha_k}{m}(F(x_k)-F^*)<\infty$ and $\|x_k-x^*\|$ converges
-- statement:
--   In the setting of the randomized incremental methods (42)–(44) (problem (5)–(6) with $X$ nonempty closed convex and $f_i,h_i$ convex; $\omega_k$ uniform on $\{1,\dots,m\}$ and independent of the past history $\mathcal F_k$; Assumption 3(b) or 4(b) with constant $c$; positive stepsizes $\alpha_k$), assume
--   $$\sum_{k=0}^\infty\alpha_k^2<\infty.$$
--   Then for each $x^*\in X^*$ there is a set $\Omega_{x^*}$ of probability 1 such that for every sample path in $\Omega_{x^*}$
--   $$\sum_{k=0}^\infty\frac{2\alpha_k}{m}\bigl(F(x_k)-F^*\bigr)<\infty,$$
--   and the sequence $\{\|x_k-x^*\|\}$ converges.
--
--   The probability-one set depends on $x^*$: the statement is "for each $x^*$, almost surely", not "almost surely, for all $x^*$". The proof of Proposition 9 passes from the first to the second through a countable dense subset of $X^*$.
--
--   **Formalization Note** $F^*=F(x^*)$ is written as $F(x^*)$. The series is stated as `Summable` of a real sequence; its terms are nonnegative from $k=1$ on (every $x_k$ with $k\ge1$ lies in $X$), so this is the paper's $\sum<\infty$. The hypotheses $\alpha_k\to0$ and $\sum\alpha_k=\infty$ of Proposition 9 are not needed for (59) and are not assumed. Components are indexed $0,\dots,m-1$.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), p. 21, §4.2, proof of Prop. 9, Eq. (59)

import Mathlib
import Definitions.Def_IncProx_Randomized_Basic

namespace IncProx.Randomized

open Filter Topology MeasureTheory

/-- Eq. (59) (proof of Proposition 9, p. 21): if Σ α_k² < ∞, then for each x* ∈ X*, with
probability 1, Σ_k (2α_k/m)(F(x_k) − F*) < ∞ and ‖x_k − x*‖ converges. -/
theorem eq59 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Problem n m) (hP : P.Standing) (A : Alg)
    (α : ℕ → ℝ) (hαpos : ∀ k, 0 < α k) (ω : ℕ → Ω → Fin m) (x : ℕ → Ω → Vec n)
    (zc gFc gHc xc : ℕ → Fin m → Ω → Vec n) (x₀ : Vec n) (c : ℝ)
    (hR : RandHyp μ P A α ω x zc gFc gHc xc x₀ c)
    (hα2 : Summable fun k => α k ^ 2) (xs : Vec n) (hxs : xs ∈ P.Xstar) :
    ∀ᵐ s ∂μ, Summable (fun k => 2 * α k / m * (P.F (x k s) - P.F xs)) ∧
      ∃ L : ℝ, Tendsto (fun k => ‖x k s - xs‖) atTop (𝓝 L) := by sorry

end IncProx.Randomized
