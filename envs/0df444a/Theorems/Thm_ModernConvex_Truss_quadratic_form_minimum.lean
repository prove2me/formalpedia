-- Prove2me | Theorems.Thm_ModernConvex_Truss_quadratic_form_minimum
-- name    : ModernConvex.Truss.quadratic_form_minimum
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:50.092153+00:00
-- url     : https://prove2.me/theorems/11556a94-5fa6-4e93-8e8d-db9a89534957
-- title:
--   Lemma 3.4.1 — minimization of a positive semidefinite quadratic form
-- statement:
--   Let $A$ be a symmetric positive semidefinite $m \times m$ real matrix, $b \in \mathbb R^m$, and consider the quadratic form
--   $$\mathcal A(v) = \tfrac12 v^TAv - b^Tv, \qquad v \in \mathbb R^m.$$
--   Then:
--
--   1. $\mathcal A$ is bounded below on $\mathbb R^m$ if and only if it attains its minimum;
--   2. $\mathcal A$ attains its minimum if and only if the equation $Av = b$ $(\ast)$ is solvable, and in that case the set of minimizers of $\mathcal A$ is exactly the set of solutions of $(\ast)$;
--   3. the minimum value of $\mathcal A$, if it exists, equals $-\tfrac12 b^Tv$, where $v$ is any solution of $(\ast)$.
--
--   This is the linear-algebra fact behind the variational description of the compliance of a truss (Proposition 3.4.4).
--
--   **Formalization Note** "Symmetric positive semidefinite" is `Matrix.PosSemidef` (which includes symmetry). "Bounded below" is `BddBelow` of the range of $\mathcal A$; "attains its minimum" is the existence of $v_0$ with $\mathcal A(v_0) \le \mathcal A(v)$ for all $v$. Item 3 is stated as: for every minimizer $v_0$ and every solution $v$ of $(\ast)$, $\mathcal A(v_0) = -\tfrac12 b^Tv$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 122, Lemma 3.4.1

import Mathlib

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, Lemma 3.4.1, p. 122. Let `𝒜(v) = ½ vᵀAv − bᵀv` be a quadratic form on `ℝᵐ`
with symmetric positive semidefinite matrix `A`. Then
(i) `𝒜` is bounded below iff it attains its minimum;
(ii) `𝒜` attains its minimum iff `Av = b` (∗) is solvable, in which case the set of minimizers of
`𝒜` is exactly the set of solutions of (∗);
(iii) the minimum value, if it exists, equals `−½ bᵀv` for any solution `v` of (∗). -/
theorem quadratic_form_minimum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef)
    (b : Fin m → ℝ) :
    let Q : (Fin m → ℝ) → ℝ := fun v => (1 / 2 : ℝ) * (v ⬝ᵥ (A *ᵥ v)) - b ⬝ᵥ v
    -- (i)
    (BddBelow (Set.range Q) ↔ ∃ v₀, ∀ v, Q v₀ ≤ Q v) ∧
    -- (ii)
    ((∃ v₀, ∀ v, Q v₀ ≤ Q v) ↔ ∃ v, A *ᵥ v = b) ∧
    ((∃ v, A *ᵥ v = b) → ∀ v₀, (∀ v, Q v₀ ≤ Q v) ↔ A *ᵥ v₀ = b) ∧
    -- (iii)
    (∀ v₀, (∀ v, Q v₀ ≤ Q v) → ∀ v, A *ᵥ v = b → Q v₀ = -((1 / 2 : ℝ) * (b ⬝ᵥ v))) := by sorry

end ModernConvex.Truss
