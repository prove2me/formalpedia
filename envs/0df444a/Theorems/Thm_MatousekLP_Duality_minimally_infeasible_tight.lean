-- Prove2me | Theorems.Thm_MatousekLP_Duality_minimally_infeasible_tight
-- name    : MatousekLP.Duality.minimally_infeasible_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:17:08.042183+00:00
-- url     : https://prove2.me/theorems/904b71f6-d2cb-47f4-954d-cd50a9ac8fb7
-- title:
--   Lemma 6.6.1 — a minimally infeasible system is tight off each dropped row
-- statement:
--   Let $Ax\le b$ be a minimally infeasible system of $m$ inequalities $a_i^{T}x\le b_i$ (it has no solution, but dropping any single inequality leaves a solvable system). For $i=1,\dots,m$ let $A^{(i)}x\le b^{(i)}$ be the subsystem obtained by dropping the $i$th inequality. Then for every $i$ there is a vector $\tilde x^{(i)}\in\mathbb{R}^n$ with
--
--   $$A^{(i)}\tilde x^{(i)}=b^{(i)},\qquad\text{i.e.}\qquad a_j^{T}\tilde x^{(i)}=b_j \ \text{ for all } j\ne i.$$
--
--   Together with Lemma 6.6.2 this yields the third proof of the Farkas lemma, variant (iii) of Proposition 6.4.3.
--
--   **Formalization Note** Rows are indexed by `Fin m` (the book's $1,\dots,m$ are $0,\dots,m-1$). Minimal infeasibility is the definition `MatousekLP.Duality.IsMinimallyInfeasible`; for $m=0$ the empty system is solvable, so the hypothesis cannot hold, exactly as in the book.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 98, Lemma 6.6.1 (definition of minimally infeasible on p. 97)

import Mathlib
import Definitions.Def_MatousekLP_Duality_MinimallyInfeasible

namespace MatousekLP.Duality

open Matrix

/-- Matoušek & Gärtner, Lemma 6.6.1 (p. 98): if `Ax ≤ b` is a minimally infeasible system of `m`
inequalities and `A⁽ⁱ⁾x ≤ b⁽ⁱ⁾` is the subsystem with the `i`th inequality dropped, then for every
`i` there is a vector `x̃⁽ⁱ⁾` with `A⁽ⁱ⁾x̃⁽ⁱ⁾ = b⁽ⁱ⁾`, i.e. `(Ax̃⁽ⁱ⁾)_j = b_j` for every `j ≠ i`. -/
theorem minimally_infeasible_tight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h : IsMinimallyInfeasible A b) :
    ∀ i : Fin m, ∃ x : Fin n → ℝ, ∀ j : Fin m, j ≠ i → (A *ᵥ x) j = b j := by sorry

end MatousekLP.Duality
