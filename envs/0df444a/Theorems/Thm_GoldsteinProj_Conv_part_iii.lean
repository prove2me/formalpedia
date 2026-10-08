-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_part_iii
-- name    : GoldsteinProj.Conv.part_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:26.788046+00:00
-- url     : https://prove2.me/theorems/71b37cce-4afd-40b5-8c9b-e78a6ea8743c
-- title:
--   THEOREM (iii), p. 709 — S convex and f″(x, h, h) ≧ μ‖h‖² (μ ≧ 0) on S give L = inf{f(x) : x ∈ C}
-- statement:
--   In the setting of part (i) (a real Hilbert space $H$, $C$ closed and convex, $P$ the projection onto $C$, $f$ bounded below and continuous on $C$, the level set $S$ of $x_0$, an open $\hat S \supseteq \operatorname{conv} S$ on which $f$ is Fréchet differentiable with $|f''(x, h, h)| \le \|h\|^2/\rho_0$, $0 < \sigma \le \rho_0$, $\sigma \le \rho_k \le 2\rho_0 - \sigma$, and $x_{k+1} = P(x_k - \rho_k \nabla f(x_k))$ from $x_0$), assume that $S$ is convex and that for some $\mu \ge 0$
--   $$f''(x, h, h) \ge \mu \|h\|^2 \qquad (x \in S,\ h \in H).$$
--   Then the limit $L$ of $f(x_k)$ is the infimum of $f$ over $C$:
--   $$L = \inf\{f(x) : x \in C\}.$$
--
--   So, under convexity on the level set, the method drives the objective to its optimal value even when no minimizer exists.
--
--   **Formalization Note** "$L = \inf$" is stated as: $L$ is the greatest lower bound of $f(C)$ (`IsGLB`), which avoids Lean's junk value of a real infimum. The claim is quantified over every limit $L$ of $f(x_k)$. Continuity of $f$ on $C$ is added as in part (i).
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, THEOREM (iii)

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, THEOREM (iii), p. 709: if `S` is convex and `f″(x, h, h) ≥ μ‖h‖²` on `S` for
some `μ ≥ 0`, then the limit `L` of `f(x_k)` is `inf {f(x) : x ∈ C}`. -/
theorem part_iii {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x)
    (μ : ℝ) (hconv : ConvexityHyp f C x0 μ) :
    ∀ L : ℝ, Tendsto (fun k => f (x k)) atTop (𝓝 L) → IsGLB (f '' C) L := by sorry

end GoldsteinProj.Conv
