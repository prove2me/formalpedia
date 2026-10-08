-- Prove2me | Theorems.Thm_FracPackCover_General_lemma_4_2
-- name    : FracPackCover.General.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:25.481102+00:00
-- url     : https://prove2.me/theorems/d84aecca-3b70-4dbb-8d06-bcfc9b0286f1
-- title:
--   Lemma 4.2 — α ≥ 2λ⁻¹ln(6mρλ⁻¹) implies 𝒢1
-- statement:
--   Let $A, b, d > 0, P$ be as in the GENERAL problem with $P$ convex, and let $\rho > 0$ satisfy $|a_i x - b_i| \le \rho d_i$ for all $x \in P$ and all $i$. Let $x \in P$ with $\lambda = \lambda(x) > 0$, and let $\alpha$ satisfy
--   $$\alpha \ge \frac{2}{\lambda}\ln\!\Big(\frac{6m\rho}{\lambda}\Big).$$
--   Then $x$ and its corresponding dual solution $y_i = \frac{1}{d_i}e^{\alpha(a_ix-b_i)/d_i}$ satisfy $(\mathcal G1)$: $\lambda\, y^t d \le 4\, y^t(Ax - b)$.
--
--   This says that the exponential dual solution makes the first relaxed optimality condition automatic once $\alpha$ is large enough, so the algorithm only needs to test $(\mathcal G2)$.
--
--   **Formalization Note.** $\lambda > 0$ is implicit in the paper ($\lambda^{-1}$ and the logarithm appear); $m \ge 1$ and the width bound $\rho$ are the section's standing assumptions.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 26, Lemma 4.2

import Mathlib
import Definitions.Def_FracPackCover_General_Basic

namespace FracPackCover.General

/-- Lemma 4.2 (p. 26). If `α ≥ 2λ⁻¹ ln(6mρλ⁻¹)`, where `λ = λ(x) > 0` for a point `x ∈ P` and
`ρ > 0` bounds the width of `P`, then `x` and its dual solution `y_i = d_i⁻¹ e^{α(a_ix − b_i)/d_i}`
satisfy (𝒢1). -/
theorem lemma_4_2 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (x : Fin n → ℝ) (hx : x ∈ P) (hlam : 0 < lam A b d x) (α : ℝ)
    (hα : 2 / lam A b d x * Real.log (6 * m * ρ / lam A b d x) ≤ α) :
    G1 A b d x (lam A b d x) (dualVec A b d α x) := by sorry

end FracPackCover.General
