-- Prove2me | Theorems.Thm_Goldstein1964_thm_ii_minimizes_of_convexOn_corrected
-- name    : Goldstein1964.thm_ii_minimizes_of_convexOn_corrected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T03:21:18.833767+00:00
-- url     : https://prove2.me/theorems/71b76b57-80ab-430f-b7a2-bae1d25a0b60
-- title:
--   THEOREM (ii), p. 709, corrected: for convex $f$, the unique cluster point minimizes $f$ on $C$
-- statement:
--   Let $H$ be a real Hilbert space, $C \subseteq H$ closed and convex, and $P$ the projection onto $C$. Let $f : H \to \mathbb R$ be bounded below, continuous on $C$ and convex on $C$. Let $x_0 \in C$, $S = \{x \in C : f(x) \le f(x_0)\}$, and $\hat S$ an open set containing the convex hull of $S$. Assume that for some $\rho_0 > 0$, for each $x \in \hat S$ and $h \in H$, $f'(x,h)$ exists in the sense of Fréchet, $f''(x,h,h)$ exists in the sense of Gâteaux, and $|f''(x,h,h)| \le \|h\|^2/\rho_0$. Let $0 < \sigma \le \rho_0$, $\sigma \le \rho_k \le 2\rho_0 - \sigma$, and $x_{k+1} = P(x_k - \rho_k \nabla f(x_k))$ with $x_0$ as above. If $S$ is compact, $z$ is the unique cluster point of $(x_k)$, and $\nabla f$ is continuous in a neighborhood of $z$, then
--
--   $$x_k \to z, \qquad z \in C, \qquad f(z) = \min_{y \in C} f(y).$$
--
--   This is the last sentence of part (ii) of the THEOREM of Goldstein, *Convex programming in Hilbert space* (1964), with convexity of $f$ on $C$ added: as printed, without convexity, the claim that $z$ minimizes $f$ on $C$ fails (e.g. $f(x) = (x^2-1)^2$ on $\mathbb R$ started at the stationary point $0$). Continuity of $f$ on $C$ is the hypothesis the existing theorem GoldsteinProj.Conv.goldstein_theorem adds for part (i).
--
--   **Formalization Note** Cluster points are norm cluster points (`MapClusterPt`); $\nabla f$ is Mathlib's `gradient`.
-- source:
--   A. A. Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), 709–710, doi:10.1090/s0002-9904-1964-11178-2, p. 709, THEOREM (ii) (with the remark on stationary points, p. 709)

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace GoldsteinProj.Conv

theorem Goldstein1964.thm_ii_minimizes_of_convexOn_corrected {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (hfconv : ConvexOn ℝ C f)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x)
    (hS : IsCompact (levelSet f C x0)) (z : H) (hz : MapClusterPt z atTop x)
    (hgrad : ∃ U ∈ 𝓝 z, ContinuousOn (gradient f) U)
    (huniq : ∀ z', MapClusterPt z' atTop x → z' = z) :
    Tendsto x atTop (𝓝 z) ∧ z ∈ C ∧ ∀ y ∈ C, f z ≤ f y := by sorry
