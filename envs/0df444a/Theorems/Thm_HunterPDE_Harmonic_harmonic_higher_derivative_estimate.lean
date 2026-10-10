-- Prove2me | Theorems.Thm_HunterPDE_Harmonic_harmonic_higher_derivative_estimate
-- name    : HunterPDE.Harmonic.harmonic_higher_derivative_estimate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:07:04.806378+00:00
-- url     : https://prove2.me/theorems/046b05ca-056c-4abb-a289-372b5af6365c
-- title:
--   Theorem 2.9 — |∂^α u(x)| ≤ nᵏ e^{k−1} k!/rᵏ · max |u| for harmonic u
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, let $u \in C^2(\Omega)$ be harmonic in $\Omega$, and let $B_r(x) \Subset \Omega$. Then for every multi-index $\alpha \in \mathbb{N}_0^n$ of order $k = |\alpha| \ge 1$
--   $$|\partial^\alpha u(x)| \le \frac{n^k e^{k-1} k!}{r^k} \max_{\overline{B}_r(x)} |u|.$$
--
--   The constant grows like $k!$ times a geometric factor, which is exactly what makes the Taylor series of $u$ converge (Theorem 2.10).
--
--   **Formalization Note.** The constant is the book's, stated exactly. The book writes "for any multi-index $\alpha \in \mathbb{N}_0^n$"; the statement adds the restriction $k \ge 1$, because at $k = 0$ the bound would read $|u(x)| \le e^{-1}\max|u|$, which fails for $u \equiv 1$, and the book's induction starts at $k = 1$ (Theorem 2.7). As in Theorem 2.7, the maximum is expressed through an arbitrary bound $M \ge |u|$ on $\overline{B}_r(x)$, equivalently. $\partial^\alpha u$ is `HunterPDE.Shared.multiDeriv u α` from the shared definition `HunterPDE.Shared.PartialDeriv` (0-based coordinates); $k$ is given with the hypothesis $\sum_i \alpha_i = k$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 23, Theorem 2.9

import Mathlib
import Definitions.Def_HunterPDE_Shared_PartialDeriv

namespace HunterPDE.Harmonic

/-- Theorem 2.9 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 23: if `u ∈ C²(Ω)` is harmonic
in the open set `Ω ⊆ ℝⁿ` and `B_r(x) ⋐ Ω`, then for every multi-index `α` of order `k = |α| ≥ 1`,
`|∂^α u(x)| ≤ (n^k e^{k-1} k! / r^k) max_{B̄_r(x)} |u|`. The maximum is expressed through an
arbitrary bound `M` of `|u|` on `B̄_r(x)`. The page states the bound for every `α ∈ ℕ₀ⁿ`; at
`k = 0` it would read `|u(x)| ≤ e^{-1} max |u|`, which fails for `u ≡ 1`, and the proof's induction
starts at `k = 1` (Theorem 2.7), so `1 ≤ k` is assumed. -/
theorem harmonic_higher_derivative_estimate {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hu : InnerProductSpace.HarmonicOnNhd u Ω)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall x r ⊆ Ω)
    (α : Fin n → ℕ) (k : ℕ) (hk : ∑ i, α i = k) (hk1 : 1 ≤ k)
    {M : ℝ} (hM : ∀ y ∈ Metric.closedBall x r, |u y| ≤ M) :
    |Shared.multiDeriv u α x| ≤ ((n : ℝ) ^ k * Real.exp 1 ^ (k - 1) * (k.factorial : ℝ) / r ^ k) * M := by sorry

end HunterPDE.Harmonic
