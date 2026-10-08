-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_part_i
-- name    : GoldsteinProj.Conv.part_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:06.084998+00:00
-- url     : https://prove2.me/theorems/592143dc-dc5c-4f72-b7c5-f65a3d4ea048
-- title:
--   THEOREM (i), p. 709 — x_k ∈ S, x_{k+1} − x_k → 0, and f(x_k) converges downward to a limit L
-- statement:
--   **Setting.** Let $H$ be a real Hilbert space with inner product $[\cdot,\cdot]$, $C \subseteq H$ closed and convex, and $P$ the projection onto $C$. Let $f : H \to \mathbb R$ be bounded below and continuous on $C$. Let $x_0 \in C$, $S = \{x \in C : f(x) \le f(x_0)\}$, and $\hat S$ an open set containing the convex hull of $S$. Assume that for some $\rho_0 > 0$, at every $x \in \hat S$ and for every $h \in H$, $f'(x, h)$ exists in the sense of Fréchet, $f''(x, h, h)$ exists in the sense of Gâteaux, and $|f''(x, h, h)| \le \|h\|^2/\rho_0$. Choose $0 < \sigma \le \rho_0$ and steps $\sigma \le \rho_k \le 2\rho_0 - \sigma$, and set
--   $$x_{k+1} = P\big(x_k - \rho_k \nabla f(x_k)\big), \qquad k \ge 0,$$
--   starting from $x_0$.
--
--   **Claim (i).** Every $x_k$ lies in $S$, $x_{k+1} - x_k \to 0$, and $f(x_k)$ is nonincreasing and converges to a limit $L$.
--
--   This is the basic convergence statement of the gradient projection method with the step-size window $[\sigma, 2\rho_0 - \sigma]$; parts (ii)–(v) build on it.
--
--   **Formalization Note** Continuity of $f$ on $C$ is added to the paper's hypotheses: without it part (i) is false (on $H = C = \mathbb R$, $P = \mathrm{id}$, $f(x) = (x-2)^2$ for $x < 1$ and $100$ for $x \ge 1$, $x_0 = 0$, $\hat S = (-1,1)$, $\rho_0 = 1/2$, $\sigma = 1/4$, $\rho_k = 1/2$, one gets $x_1 = 2 \notin S$). "Bounded below" is read as bounded below on $H$, as the paper's "Assume $f$ is bounded below" for a function on $H$. "Converges downward" is formalized as antitone plus convergent.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, THEOREM (i)

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, THEOREM (i), p. 709: the iterates stay in `S`, `x_{k+1} - x_k → 0`, and
`f(x_k)` converges downward to a limit `L`. -/
theorem part_i {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCc : IsClosed C) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (hbdd : BddBelow (Set.range f)) (hfC : ContinuousOn f C)
    (x0 : H) (hx0 : x0 ∈ C)
    (Shat : Set H) (hShat_open : IsOpen Shat) (hShat : convexHull ℝ (levelSet f C x0) ⊆ Shat)
    (ρ0 : ℝ) (hρ0 : 0 < ρ0) (hD : SecondDerivBound f Shat ρ0)
    (σ : ℝ) (hσ : 0 < σ) (hσρ0 : σ ≤ ρ0) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x) :
    (∀ k, x k ∈ levelSet f C x0) ∧ Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) ∧
      ∃ L : ℝ, Antitone (fun k => f (x k)) ∧ Tendsto (fun k => f (x k)) atTop (𝓝 L) := by sorry

end GoldsteinProj.Conv
