-- Prove2me | Theorems.Thm_NumStochOpt_Nonstationary_theorem_6_3_nonstationary_projected_subgradient
-- name    : NumStochOpt.Nonstationary.theorem_6_3_nonstationary_projected_subgradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T19:33:51.186876+00:00
-- url     : https://prove2.me/theorems/2d58517d-e4f7-49db-b672-5752e6a34170
-- title:
--   Theorem 6.3 — the projected subgradient method tracks $\min_X f^0$ when $F^0(\cdot,s) \to f^0$ uniformly
-- statement:
--   This is the basic convergence theorem for **nonstationary optimization**: the objective changes with the iteration number, and the method has to follow it.
--
--   Let $F^0(\cdot, s) : \mathbb R^n \to \mathbb R$, $s = 0, 1, \dots$, and $f^0 : \mathbb R^n \to \mathbb R$ be functions and $X \subseteq \mathbb R^n$ a set such that
--
--   1. $F^0(\cdot, s)$ and $f^0$ are convex continuous functions;
--   2. $X$ is a nonempty convex compact set;
--   3. $F^0(x, s) \to f^0(x)$ uniformly in $x \in X$ as $s \to \infty$;
--   4. $g_s$ is a subgradient of $F^0(\cdot, s)$ at $x^s$ (the book's $F^0_x(x^s, s)$), and $\|g_s\| \le C$ for all $s$.
--
--   Let $x^0 \in \mathbb R^n$ and
--   $$
--   x^{s+1} = \pi_X\bigl[x^s - \rho_s g_s\bigr], \qquad s = 0, 1, \dots, \tag{6.41}
--   $$
--   where $\pi_X$ is the Euclidean projection onto $X$ and the step sizes satisfy $\rho_s \ge 0$, $\rho_s \to 0$ and $\sum_{s=0}^\infty \rho_s = \infty$. Then
--
--   $$
--   F^0(x^s, s) \longrightarrow f^0(x^*) = \min\{f^0(x) \mid x \in X\} \qquad (s \to \infty),
--   $$
--   where $x^*$ is any minimizer of $f^0$ on $X$.
--
--   The method never sees $f^0$: it takes one subgradient step on the current approximation $F^0(\cdot, s)$ at each iteration, so that approximation and optimization proceed simultaneously. The iteration is not monotone in any of the functions involved, which is why the proof goes through the convergence criterion of Theorem 6.4.
--
--   **Formalization Note** The theorem is deterministic. The subgradient inequality is required on all of $\mathbb R^n$: $F^0(y, s) \ge F^0(x^s, s) + \langle g_s, y - x^s\rangle$ for every $y$. The book prints neither $\rho_s \ge 0$ nor $X \neq \varnothing$; both are added (step sizes are nonnegative throughout the chapter, and the minimum over $X$ must exist). The limit is written as $\inf f^0(X)$, which for a continuous $f^0$ on a nonempty compact $X$ is the minimum. $\sum_s \rho_s = \infty$ is stated as divergence of the partial sums to $+\infty$.
-- source:
--   Yu. Ermoliev, "Stochastic Quasigradient Methods", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 6, pp. 153–154, Theorem 6.3 and Eq. (6.41)

import Mathlib
import Definitions.Def_NumStochOpt_QuasiFejer_ProjectionMethod

open scoped RealInnerProductSpace
open Filter Topology

namespace NumStochOpt.Nonstationary

/-- Theorem 6.3 (Ermoliev, Ch. 6 of Ermoliev & Wets (1988), pp. 153–154). Let `F⁰(·, s)` and
`f⁰` be convex continuous functions on `ℝⁿ`, `X ⊆ ℝⁿ` a nonempty convex compact set, and
`F⁰(·, s) → f⁰` uniformly on `X`. Let `g_s` be a subgradient of `F⁰(·, s)` at `x^s` with
`‖g_s‖ ≤ C` for all `s`, and let `x^{s+1} = π_X[x^s - ρ_s g_s]` (6.41) with `ρ_s ≥ 0`,
`ρ_s → 0`, `∑_s ρ_s = ∞`. Then `F⁰(x^s, s) → min {f⁰(x) | x ∈ X}`. -/
theorem theorem_6_3_nonstationary_projected_subgradient {n : ℕ}
    (F : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → ℝ) (C : ℝ)
    (hFconv : ∀ s, ConvexOn ℝ Set.univ (F s)) (hFcont : ∀ s, Continuous (F s))
    (hfconv : ConvexOn ℝ Set.univ f) (hfcont : Continuous f)
    (hXconv : Convex ℝ X) (hXcpt : IsCompact X) (hXne : X.Nonempty)
    (hunif : TendstoUniformlyOn F f atTop X)
    (hsub : ∀ s y, F s (x s) + ⟪g s, y - x s⟫ ≤ F s y)
    (hbound : ∀ s, ‖g s‖ ≤ C)
    (hrec : ∀ s, x (s + 1) = NumStochOpt.QuasiFejer.projX X (x s - ρ s • g s))
    (hρnn : ∀ s, 0 ≤ ρ s) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hρsum : Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s) atTop atTop) :
    Tendsto (fun s => F s (x s)) atTop (𝓝 (sInf (f '' X))) := by sorry

end NumStochOpt.Nonstationary
