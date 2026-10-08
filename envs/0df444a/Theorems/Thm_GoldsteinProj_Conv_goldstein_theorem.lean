-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_goldstein_theorem
-- name    : GoldsteinProj.Conv.goldstein_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:39.14986+00:00
-- url     : https://prove2.me/theorems/f272ffde-2bd6-4617-ac13-bfa198825b6b
-- title:
--   THEOREM (i)–(v), pp. 709–710 — gradient projection stays in S, f(x_k) ↓ L; under convexity L = inf_C f, weak cluster points minimize, strong convexity gives x_k → z
-- statement:
--   **Setting.** Let $H$ be a real Hilbert space with inner product $[\cdot,\cdot]$, $C \subseteq H$ closed and convex, and $P$ the projection onto $C$ ($P(x)$ is the closest point of $C$ to $x$). Let $f : H \to \mathbb R$ be bounded below and continuous on $C$. Let $x_0 \in C$, $S = \{x \in C : f(x) \le f(x_0)\}$, and $\hat S$ an open set containing the convex hull of $S$. Assume that for some $\rho_0 > 0$, for each $x \in \hat S$ and $h \in H$, $f'(x, h)$ exists in the sense of Fréchet, $f''(x, h, h)$ exists in the sense of Gâteaux, and
--   $$|f''(x, h, h)| \le \frac{\|h\|^2}{\rho_0}.$$
--   Choose $0 < \sigma \le \rho_0$ and $\sigma \le \rho_k \le 2\rho_0 - \sigma$, and set
--   $$x_{k+1} = P\big(x_k - \rho_k \nabla f(x_k)\big), \qquad k \ge 0.$$
--   Call $z \in C$ stationary if $P(z - \rho\nabla f(z)) = z$ for all $\rho > 0$.
--
--   **Theorem.** There is $L \in \mathbb R$ such that:
--   1. (i) every $x_k$ lies in $S$, $x_{k+1} - x_k \to 0$, and $f(x_k)$ is nonincreasing with limit $L$;
--   2. (ii) if $S$ is compact: every cluster point $z$ of $(x_k)$ near which $\nabla f$ is continuous is stationary, and if $z$ is the only cluster point then $x_k \to z$;
--   3. (iii) if $S$ is convex and $f''(x, h, h) \ge \mu\|h\|^2$ for all $x \in S$, $h \in H$ and some $\mu \ge 0$, then $L = \inf\{f(x) : x \in C\}$;
--   4. (iv) under (iii) with $S$ bounded, every weak cluster point of $(x_k)$ minimizes $f$ on $C$;
--   5. (v) under (iii) with $\mu > 0$ and $\nabla f$ bounded on $S$, there is $z \in S$ with $f(z) = L$, $x_k \to z$, and $z$ is the unique minimizer of $f$ on $C$.
--
--   This is the convergence theorem for the gradient projection method in Hilbert space with step sizes in $[\sigma, 2\rho_0 - \sigma]$, where $1/\rho_0$ bounds the curvature of $f$ near the level set.
--
--   **Formalization Note** Continuity of $f$ on $C$ is added to the paper's hypotheses because part (i) is false without it: on $H = C = \mathbb R$ with $P = \mathrm{id}$, $f(x) = (x-2)^2$ for $x < 1$ and $100$ for $x \ge 1$, $x_0 = 0$, $\hat S = (-1, 1)$, $\rho_0 = 1/2$, $\sigma = 1/4$, $\rho_k = 1/2$, one gets $x_1 = 2$ and $f(x_1) = 100 > f(x_0)$. The last clause of (ii), "and $z$ minimizes $f$ on $C$", is false for nonconvex $f$ and is left out here; it is stated under convexity of $f$ on $C$ in the companion item `part_ii_minimizes_of_convexOn`. "If $z$ is unique" in (ii) means that $z$ is the only cluster point; in (v) it means that $z$ is the only minimizer. The infimum in (iii) is stated as a greatest lower bound (`IsGLB`). Weak cluster points are cluster points in `WeakSpace ℝ H`. The iteration is started at $x_0$.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), pp. 709–710, THEOREM (i)–(v)

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, THEOREM (i)–(v), pp. 709–710 (with `f` continuous on `C` added, and the last
clause of (ii) left to the companion item `part_ii_minimizes_of_convexOn`). All parts share the
limit `L` of `f(x_k)`. -/
theorem goldstein_theorem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x) :
    ∃ L : ℝ,
      -- (i)
      ((∀ k, x k ∈ levelSet f C x0) ∧ Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) ∧
        Antitone (fun k => f (x k)) ∧ Tendsto (fun k => f (x k)) atTop (𝓝 L)) ∧
      -- (ii), without its last clause
      (IsCompact (levelSet f C x0) →
        (∀ z, MapClusterPt z atTop x → (∃ U ∈ 𝓝 z, ContinuousOn (gradient f) U) →
            IsStationary f C P z) ∧
        (∀ z, MapClusterPt z atTop x → (∀ z', MapClusterPt z' atTop x → z' = z) →
            Tendsto x atTop (𝓝 z))) ∧
      -- (iii)
      (∀ μ : ℝ, ConvexityHyp f C x0 μ → IsGLB (f '' C) L) ∧
      -- (iv)
      (∀ μ : ℝ, ConvexityHyp f C x0 μ → Bornology.IsBounded (levelSet f C x0) →
        ∀ z, IsWeakClusterPt x z → z ∈ C ∧ ∀ y ∈ C, f z ≤ f y) ∧
      -- (v)
      (∀ μ : ℝ, 0 < μ → ConvexityHyp f C x0 μ →
        (∃ M : ℝ, ∀ y ∈ levelSet f C x0, ‖gradient f y‖ ≤ M) →
        ∃ z ∈ levelSet f C x0, f z = L ∧ Tendsto x atTop (𝓝 z) ∧
          (∀ y ∈ C, f z ≤ f y) ∧
          ∀ y ∈ C, (∀ w ∈ C, f y ≤ f w) → y = z) := by sorry

end GoldsteinProj.Conv
