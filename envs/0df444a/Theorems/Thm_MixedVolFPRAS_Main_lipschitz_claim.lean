-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_lipschitz_claim
-- name    : MixedVolFPRAS.Main.lipschitz_claim
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:32:09.53121+00:00
-- url     : https://prove2.me/theorems/11e8421c-e8ad-404a-a54e-4f9ff82e745b
-- title:
--   §5, proof of Theorem 1.2 (Lipschitz claim) — F(y) = log Z_β(e^y) − ⟨y, 1⟩ has an n²-Lipschitz gradient on ℝⁿ
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb{R}^n$ be convex bodies and $\beta\ge0$. The function
--
--   $$F(y)=\log Z_\beta(e^y)-\langle y,\mathbf 1\rangle,\qquad y\in\mathbb{R}^n,$$
--
--   is differentiable on $\mathbb{R}^n$ and its gradient is $n^2$-Lipschitz:
--
--   $$\|\nabla_{\mathbb{R}^n}F(y)-\nabla_{\mathbb{R}^n}F(z)\|_2\le n^2\|y-z\|_2\qquad\forall y,z\in\mathbb{R}^n.$$
--
--   The claim lets inexact projected gradient descent (Proposition 2.18) minimize (16) in polynomial time.
--
--   Differences from the source:
--   - generalization: the claim is made for the proof's $\beta=\varepsilon/(10n^2)$ ($0<\varepsilon<1$), $n\ge3$, and bodies translated so that $r_iB_2^n\subseteq K_i\subseteq R_iB_2^n$ → every $\beta\ge0$, every $n$ and all convex bodies; reason: the proof uses only that $Z_\beta$ is a homogeneous degree-$n$ polynomial with nonnegative coefficients, which holds for all $\beta\ge0$; specializing gives the paper's claim.
--   - encoding: "has an $n^2$-Lipschitz gradient" → `Differentiable ℝ F ∧ ∀ y z, ‖gradient F y − gradient F z‖ ≤ n² ‖y − z‖` on `EuclideanSpace ℝ (Fin n)`; reason: makes the differentiability explicit.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 25, §5, proof of Theorem 1.2 (Lipschitz claim)

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_Balancing

namespace MixedVolFPRAS.Main

/-- **§5, proof of Theorem 1.2 (Lipschitz claim).** For convex bodies `K₁, …, Kₙ` in `ℝⁿ` and
`β ≥ 0`, `F(y) = log Z_β(e^y) − ⟨y, 1⟩` is differentiable on `ℝⁿ` and its gradient is
`n²`-Lipschitz: `‖∇F(y) − ∇F(z)‖₂ ≤ n² ‖y − z‖₂` for all `y, z ∈ ℝⁿ`. -/
theorem lipschitz_claim {n : ℕ} (K : Fin n → Set (E n)) (hK : ∀ i, IsConvexBody (K i))
    (β : ℝ) (hβ : 0 ≤ β) :
    Differentiable ℝ (fun y : E n => Real.log (Zbeta K β (fun i => Real.exp (y i))) - ∑ i, y i) ∧
      ∀ y z : E n,
        ‖gradient (fun y : E n => Real.log (Zbeta K β (fun i => Real.exp (y i))) - ∑ i, y i) y -
          gradient (fun y : E n => Real.log (Zbeta K β (fun i => Real.exp (y i))) - ∑ i, y i) z‖ ≤
          (n : ℝ) ^ 2 * ‖y - z‖ := by sorry

end MixedVolFPRAS.Main
