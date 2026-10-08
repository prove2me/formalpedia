-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_hoffman_theorem
-- name    : HoffmanBound.ErrorBound.hoffman_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:38:44.132421+00:00
-- url     : https://prove2.me/theorems/73fc94b7-e4fd-43a2-9230-b1d670a21f7b
-- title:
--   Hoffman's theorem — if Ax ≦ b is consistent, there is c > 0 with Fₙ(x − x₀) ≦ c Fₘ((Ax − b)⁺) for some solution x₀
-- statement:
--   Let $A$ be a real $m\times n$ matrix and $b\in\mathbb R^m$, and suppose the system $Ax\le b$ is consistent. Let $F_n$ on $\mathbb R^n$ and $F_m$ on $\mathbb R^m$ be positive homogeneous functions in the sense of (3): continuous, nonnegative, zero only at the origin, and $F(\alpha x)=\alpha F(x)$ for $\alpha\ge 0$. Then there exists a constant $c>0$ such that for every $x\in\mathbb R^n$ there exists a solution $x_0$ of $Ax\le b$ with
--   $$
--   F_n(x-x_0)\le c\,F_m\bigl((Ax-b)^+\bigr).
--   $$
--
--   A point that almost satisfies the system is close to a solution, by an amount at most a fixed multiple of the violation $(Ax-b)^+$. The constant $c$ depends on $A$, $b$, $F_n$ and $F_m$ but not on $x$.
--
--   **Formalization Note** The page prints the display as "$cF_m\,(Ax-b)^+)$", dropping an opening parenthesis; the proof's last line prints $F_m((Ax-b)^+)$, which is the reading used. $F_n$ and $F_m$ are arbitrary functions satisfying (3), not necessarily norms.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), p. 263 (PDF p. 1), Theorem (Section 2)

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, Theorem (Section 2). If `Ax ≤ b` is consistent and `F_n`, `F_m` satisfy
(3), there is a constant `c > 0` such that for every `x` there is a solution `x₀` with
`F_n(x - x₀) ≤ c F_m((Ax - b)⁺)`. The constant is chosen before `x`. -/
theorem hoffman_theorem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty)
    (Fn : (Fin n → ℝ) → ℝ) (Fm : (Fin m → ℝ) → ℝ)
    (hFn : IsPosHomogeneous Fn) (hFm : IsPosHomogeneous Fm) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      Fn (x - x₀) ≤ c * Fm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound
