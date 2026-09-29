-- Prove2me | Theorems.Thm_IPProximity_Eisenbrand_fractional_part_split
-- name    : IPProximity.Eisenbrand.fractional_part_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:32:29.813892+00:00
-- url     : https://prove2.me/theorems/c7ff5cc3-373f-48d5-b377-1aaff9d4cccd
-- title:
--   Proof of Theorem 3.3 — the fractional part of a vertex splits into m vectors of ℓ∞-norm ≤ Δ
-- statement:
--   Let $m,n\ge 0$, let $A\in\mathbb Z^{m\times n}$, $b\in\mathbb Z^m$, $c\in\mathbb Z^n$ and $u\in\mathbb N^n$. The integer program (10) of Eisenbrand and Weismantel is
--   $$\max\{c^{T}x : Ax=b,\ 0\le x\le u,\ x\in\mathbb Z^n\},$$
--   and its linear programming (LP) relaxation is the same problem with $x\in\mathbb R^n$. Let $\Delta\in\mathbb N$ bound the entries, $|a_{ij}|\le\Delta$. Let $x^*$ be a vertex (extreme point) of the LP feasible region $P(A,b,u)$ and $z\in\mathbb Z^n$ any integer vector. Round $x^*$ towards $z$:
--   $$\lfloor x^*\rceil_i=\begin{cases}\lceil x^*_i\rceil & \text{if } z_i>x^*_i,\\ \lfloor x^*_i\rfloor & \text{if } z_i\le x^*_i,\end{cases}\qquad \{x^*\}=x^*-\lfloor x^*\rceil .$$
--   Then
--   1. $\|-A\{x^*\}\|_\infty\le\Delta\cdot m$, and
--   2. there are integer vectors $w_1,\dots,w_m\in\mathbb Z^m$ with $\|w_j\|_\infty\le\Delta$ for all $j$ and
--   $$-A\{x^*\}=w_1+\dots+w_m .$$
--
--   This is the step of the proof of Theorem 3.3 where the vertex hypothesis enters: it turns the fractional residue of $x^*$ into $m$ short integer vectors that complete the zero-sum sequence (17) fed to the Steinitz lemma.
--
--   **Formalization Note** The paper takes $z=z^*$, an optimal integer solution; the statement holds for every integer $z$ and is stated so. The page justifies the bound by "$x^*$ has at most $m$ positive entries"; for (10) with upper bounds the relevant fact is that a vertex has at most $m$ coordinates strictly between $0$ and $u_i$, and the Lean hypothesis is the extreme-point property itself.
-- source:
--   Eisenbrand & Weismantel, Proximity Results and Faster Algorithms for Integer Programming Using the Steinitz Lemma, ACM Trans. Algorithms 16(1), Article 5 (2019), pp. 5:8–5:9, proof of Theorem 3.3 (rounding before Eq. (15); w_1, …, w_m before Eq. (17))

import Mathlib
import Definitions.Def_IPProximity_Eisenbrand_lpPolytope

namespace IPProximity.Eisenbrand

/-- Proof of Theorem 3.3 (pp. 5:8–5:9): round a vertex `x` of the LP relaxation of (10) towards
an integer vector `z` (`rᵢ = ⌈xᵢ⌉` if `zᵢ > xᵢ`, `rᵢ = ⌊xᵢ⌋` otherwise) and let `{x} = x - r`.
Then `‖-A{x}‖∞ ≤ Δ·m`, and `-A{x}` is the sum of `m` integer vectors of `ℓ∞`-norm at most `Δ`. -/
theorem fractional_part_split {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (u : Fin n → ℕ) (Δ : ℕ) (hΔ : ∀ i j, |A i j| ≤ (Δ : ℤ))
    (x : Fin n → ℝ) (hx : x ∈ Set.extremePoints ℝ (lpPolytope A b u)) (z : Fin n → ℤ) :
    let r : Fin n → ℤ := fun i => if x i < (z i : ℝ) then ⌈x i⌉ else ⌊x i⌋
    let frac : Fin n → ℝ := fun i => x i - (r i : ℝ)
    (∀ i, |(-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i| ≤ (Δ : ℝ) * m) ∧
      ∃ w : Fin m → Fin m → ℤ, (∀ j i, |w j i| ≤ (Δ : ℤ)) ∧
        ∀ i, ∑ j, (w j i : ℝ) = (-(Matrix.mulVec (A.map (Int.cast : ℤ → ℝ)) frac)) i := by sorry

end IPProximity.Eisenbrand
