-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_part_ii
-- name    : GoldsteinProj.Conv.part_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:25.32598+00:00
-- url     : https://prove2.me/theorems/e9afaf31-1f33-4ee4-8ec8-60d026402d49
-- title:
--   THEOREM (ii), p. 709 — S compact: cluster points where ∇f is locally continuous are stationary; a unique cluster point is the limit
-- statement:
--   In the setting of part (i) (a real Hilbert space $H$, $C$ closed and convex, $P$ the projection onto $C$, $f$ bounded below and continuous on $C$, the level set $S$ of $x_0$, an open $\hat S \supseteq \operatorname{conv} S$ on which $f$ is Fréchet differentiable with $|f''(x, h, h)| \le \|h\|^2/\rho_0$, $0 < \sigma \le \rho_0$, $\sigma \le \rho_k \le 2\rho_0 - \sigma$, and $x_{k+1} = P(x_k - \rho_k \nabla f(x_k))$ from $x_0$), assume in addition that $S$ is compact. Then:
--   1. if $z$ is a cluster point of $(x_k)$ and $\nabla f$ is continuous on some neighbourhood of $z$, then $z$ is stationary: $P(z - \rho \nabla f(z)) = z$ for all $\rho > 0$;
--   2. if $z$ is a cluster point of $(x_k)$ and it is the only one, then $x_k \to z$.
--
--   **Formalization Note** The paper's (ii) ends "and $z$ minimizes $f$ on $C$". That clause is false without convexity ($f$ smooth on $\mathbb R$ with $f = x^2$ on $[-1, 1]$ and a deeper minimum elsewhere, started at $x_0 = 0.1$, has the unique cluster point $0$, which is stationary but not a minimizer), so it is stated separately, under convexity of $f$ on $C$, in the companion item `part_ii_minimizes_of_convexOn`. "If $z$ is unique" is read as: $z$ is the only cluster point of $(x_k)$. Continuity of $f$ on $C$ is added as in part (i).
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, THEOREM (ii), without its last clause

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, THEOREM (ii), p. 709, without its last clause: if `S` is compact, every cluster
point `z` of `(x_k)` near which `∇f` is continuous is stationary, and if `z` is the only cluster
point then `x_k → z`. -/
theorem part_ii {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x)
    (hS : IsCompact (levelSet f C x0)) :
    (∀ z, MapClusterPt z atTop x → (∃ U ∈ 𝓝 z, ContinuousOn (gradient f) U) →
        IsStationary f C P z) ∧
      (∀ z, MapClusterPt z atTop x → (∀ z', MapClusterPt z' atTop x → z' = z) →
        Tendsto x atTop (𝓝 z)) := by sorry

end GoldsteinProj.Conv
