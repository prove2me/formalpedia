-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_moment_curve_orthogonal
-- name    : MegiddoLP.FixedDim.moment_curve_orthogonal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:08:58.265394+00:00
-- url     : https://prove2.me/theorems/d930d603-0434-4ae7-b13e-de8721b4493c
-- title:
--   $v(\epsilon)=(1,\epsilon,\dots,\epsilon^{d-1})$ is orthogonal to some $a_i$ for at most $n(d-1)$ values of $\epsilon$
-- statement:
--   Let $a_1,\dots,a_n\in\mathbb{R}^d$ be nonzero vectors and, for a real $\epsilon$, let $v(\epsilon)=(1,\epsilon,\epsilon^2,\dots,\epsilon^{d-1})^T$. Let
--
--   $$E=\{\epsilon\in\mathbb{R}:\ a_i^Tv(\epsilon)=0\ \text{for some } i\}.$$
--
--   Then:
--
--   1. $E$ is finite and has at most $n(d-1)$ elements;
--   2. there is a nonsingular $d\times d$ matrix $M$ such that every coordinate of every transformed normal $M^Ta_i$ is nonzero.
--
--   Part 2 is the paper's "a basis for $R^d$ relative to which $a_{ij}\ne0$ for all $i,j$", with the change of coordinates $x=My$, under which the hyperplane $a^Tx=b$ becomes $(M^Ta)^Ty=b$. Each $a_i^Tv(\epsilon)$ is a nonzero polynomial in $\epsilon$ of degree at most $d-1$, which gives part 1. The basis vectors are then chosen as $v(\epsilon)$ for values of $\epsilon$ outside $E$. The search procedure uses this normalization so that every hyperplane meets the $(x_1,x_2)$ plane in a line.
--
--   **Formalization Note** Both finiteness and the cardinality bound are stated, because Lean's `Set.ncard` of an infinite set is $0$. The paper's $O(n)$ running time for finding the basis is not formalized. The hypothesis $a_i\ne0$ is the paper's standing assumption on the hyperplanes (p. 118). Without it the claim is false, since $0$ is orthogonal to every $v(\epsilon)$.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §3.2, p. 119 (the v(ε) observation); coordinate change x = My, p. 118

import Mathlib

/-!
Megiddo, J. ACM 31 (1984), §3.2 p. 119: `v(ε) = (1, ε, …, ε^{d-1})ᵀ` is orthogonal to some
`aᵢ` for at most `n(d - 1)` values of `ε`, and hence there is a basis of `ℝ^d` relative to
which every coefficient `a_ij` is nonzero.
-/

namespace MegiddoLP.FixedDim

/-- **The `v(ε)` observation.** Let `a₁, …, aₙ ∈ ℝ^d` be nonzero. The set of reals `ε` for
which `v(ε) = (ε^0, ε^1, …, ε^{d-1})` is orthogonal to some `aᵢ` is finite with at most
`n (d - 1)` elements; and there is an invertible `d × d` matrix `M` (the change of basis
`x = M y`, under which `aᵢ` becomes `Mᵀ aᵢ`) such that every coordinate of every `Mᵀ aᵢ`
is nonzero. -/
theorem moment_curve_orthogonal (n d : ℕ) (a : Fin n → Fin d → ℝ) (ha : ∀ i, a i ≠ 0) :
    {ε : ℝ | ∃ i, a i ⬝ᵥ (fun j : Fin d => ε ^ (j : ℕ)) = 0}.Finite ∧
    {ε : ℝ | ∃ i, a i ⬝ᵥ (fun j : Fin d => ε ^ (j : ℕ)) = 0}.ncard ≤ n * (d - 1) ∧
    ∃ M : Matrix (Fin d) (Fin d) ℝ, IsUnit M.det ∧
      ∀ i j, (M.transpose.mulVec (a i)) j ≠ 0 := by sorry

end MegiddoLP.FixedDim
