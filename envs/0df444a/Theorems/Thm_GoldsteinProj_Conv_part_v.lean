-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_part_v
-- name    : GoldsteinProj.Conv.part_v
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:32.231985+00:00
-- url     : https://prove2.me/theorems/fb481609-29eb-4dc0-ba3a-f66285fe0103
-- title:
--   THEOREM (v), p. 710 — under (iii) with μ > 0 and ∇f bounded on S: f(z) = L for some z ∈ S, x_k → z, z unique
-- statement:
--   In the setting of part (i) (a real Hilbert space $H$, $C$ closed and convex, $P$ the projection onto $C$, $f$ bounded below and continuous on $C$, the level set $S$ of $x_0$, an open $\hat S \supseteq \operatorname{conv} S$ on which $f$ is Fréchet differentiable with $|f''(x, h, h)| \le \|h\|^2/\rho_0$, $0 < \sigma \le \rho_0$, $\sigma \le \rho_k \le 2\rho_0 - \sigma$, and $x_{k+1} = P(x_k - \rho_k \nabla f(x_k))$ from $x_0$), assume the hypothesis of (iii) with $\mu > 0$ — $S$ convex and $f''(x, h, h) \ge \mu \|h\|^2$ on $S$ — and that $\nabla f$ is bounded on $S$. Then there is $z \in S$ such that
--   1. $f(x_k) \to f(z)$, i.e. $f(z) = L$;
--   2. $x_k \to z$ in norm;
--   3. $z$ minimizes $f$ on $C$, and every other minimizer equals $z$.
--
--   Under strong convexity on the level set the iterates themselves converge, strongly, to the unique solution.
--
--   **Formalization Note** "$z$ is unique" is read as uniqueness of the minimizer of $f$ on $C$, which is what the paper's proof establishes ("$f(x) - f(z) \ge \frac12\mu\|x - z\|^2$; and therefore $z$ is unique"). Continuity of $f$ on $C$ is added as in part (i).
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 710, THEOREM (v)

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, THEOREM (v), p. 710: under the hypotheses of (iii) with `μ > 0` and `∇f` bounded
on `S`, there is `z ∈ S` with `f(z) = L`, `x_k → z`, and `z` is the unique minimizer of `f` on `C`. -/
theorem part_v {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x)
    (μ : ℝ) (hμ : 0 < μ) (hconv : ConvexityHyp f C x0 μ)
    (hgrad : ∃ M : ℝ, ∀ y ∈ levelSet f C x0, ‖gradient f y‖ ≤ M) :
    ∃ z ∈ levelSet f C x0, Tendsto (fun k => f (x k)) atTop (𝓝 (f z)) ∧ Tendsto x atTop (𝓝 z) ∧
      (∀ y ∈ C, f z ≤ f y) ∧
      ∀ y ∈ C, (∀ w ∈ C, f y ≤ f w) → y = z := by sorry

end GoldsteinProj.Conv
