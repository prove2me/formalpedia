-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_part_iv
-- name    : GoldsteinProj.Conv.part_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:31.980295+00:00
-- url     : https://prove2.me/theorems/3e365dff-beda-4a31-9830-2b40c7e2df09
-- title:
--   THEOREM (iv), p. 709 — under (iii) with S bounded, weak cluster points of {x_k} minimize f on C
-- statement:
--   In the setting of part (i) (a real Hilbert space $H$, $C$ closed and convex, $P$ the projection onto $C$, $f$ bounded below and continuous on $C$, the level set $S$ of $x_0$, an open $\hat S \supseteq \operatorname{conv} S$ on which $f$ is Fréchet differentiable with $|f''(x, h, h)| \le \|h\|^2/\rho_0$, $0 < \sigma \le \rho_0$, $\sigma \le \rho_k \le 2\rho_0 - \sigma$, and $x_{k+1} = P(x_k - \rho_k \nabla f(x_k))$ from $x_0$), assume the hypothesis of (iii) ($S$ convex, $f''(x, h, h) \ge \mu\|h\|^2$ on $S$ for some $\mu \ge 0$) and that $S$ is bounded. Then every weak cluster point $z$ of $(x_k)$ minimizes $f$ on $C$:
--   $$z \in C \quad\text{and}\quad f(z) \le f(y) \ \text{ for all } y \in C.$$
--
--   In infinite dimensions bounded sequences need not have norm-convergent subsequences, but they do have weak cluster points; this part says those are solutions.
--
--   **Formalization Note** A weak cluster point is a cluster point in Mathlib's weak topology `WeakSpace ℝ H`; this covers limits of weakly convergent subsequences. Continuity of $f$ on $C$ is added as in part (i).
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, THEOREM (iv)

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, THEOREM (iv), p. 709: under the hypotheses of (iii) with `S` bounded, every weak
cluster point of `(x_k)` minimizes `f` on `C`. -/
theorem part_iv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x)
    (μ : ℝ) (hconv : ConvexityHyp f C x0 μ) (hSb : Bornology.IsBounded (levelSet f C x0)) :
    ∀ z, IsWeakClusterPt x z → z ∈ C ∧ ∀ y ∈ C, f z ≤ f y := by sorry

end GoldsteinProj.Conv
