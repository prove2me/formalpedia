-- Prove2me | Theorems.Thm_MIQPInNP_SmallSol_proposition_4
-- name    : MIQPInNP.SmallSol.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:45.740735+00:00
-- url     : https://prove2.me/theorems/a48cc118-dc48-413d-8164-15ad4b2a4e18
-- title:
--   Proposition 4, p. 3 — the mixed-integer points of a pointed rational polyhedron are a finite union of polytope + int.cone(R_K) pieces of small complexity
-- statement:
--   Let $P = \{x : Ax\le b\}\subseteq\mathbb R^{p+q}$ be a rational pointed polyhedron, i.e. $A\in\mathbb Q^{m\times(p+q)}$, $b\in\mathbb Q^m$ and, if $P\neq\emptyset$, $\{x : Ax = 0\} = \{0\}$. There is a single polynomial $g$, fixed before $p$, $q$, $m$ and the data, such that there exist
--
--   - finitely many polytopes $P_i = \{x : A_i x\le b_i\}$ (bounded polyhedra with rational descriptions), and
--   - a finite family $\mathcal K$ of finite sets $R_K$ of integral vectors, each spanning an extreme ray of the recession cone $\{x : Ax\le 0\}$ of $P$,
--
--   with the following properties:
--
--   1. $$P\cap(\mathbb Z^p\times\mathbb R^q) = \bigcup_{i,\ K\in\mathcal K}\big(P_i + \operatorname{int.cone}(R_K)\big),$$ the union running over all pairs $(i,K)$;
--   2. each description $[A_i\ b_i]$ and each vector of each $R_K$ has bit-size at most $g(\operatorname{size}[A\ b])$;
--   3. all vectors in every $R_K$ are integral;
--   4. each cone $\operatorname{cone}(R_K)$ is simple: the vectors of $R_K$ are linearly independent.
--
--   The decomposition writes any mixed-integer linear set as an overlapping union of sets affinely isomorphic to some $\mathbb Z_+^{n'}$, which the proof of Theorem 1 uses to reduce to a single polytope plus the integer cone of a simple cone.
--
--   **Formalization Note** The polynomial is quantified before all dimensions and data. Polytopes are given by inequality descriptions and their complexity is that of the description, the paper's definition on p. 2. An empty $P$ is allowed (empty families).
--
--   Differences from the source:
--   - encoding: "each cone $\operatorname{cone}(R_K)$ is simple" → the vectors of $R_K$ are linearly independent; reason: for distinct extreme-ray generators of a pointed polyhedron, the number of extreme rays of $\operatorname{cone}(R_K)$ equals its dimension exactly when $R_K$ is linearly independent.
--   - encoding: "subsets of extreme rays of $P$" with "all vectors in $R_K$ integral" → integer vectors whose real images span extreme rays of $\{x : Ax\le 0\}$; reason: the extreme rays of a polyhedron are those of its recession cone, and the proof (p. 4) uses integral scalings of them.
--   - encoding: "pointed polyhedron" → if $P\neq\emptyset$ then $\{x : Ax = 0\}=\{0\}$; reason: for a non-empty polyhedron this is equivalent to having a vertex, and the empty polyhedron (pointed, and trivial for the proposition) is not excluded.
--   - encoding: "polynomial", "complexity" and "$[A\ b]$-small" → `Polynomial ℕ` evaluated at Schrijver's bit-size of $[A\ b]$; reason: polynomially equivalent to any standard encoding.
-- source:
--   Del Pia, Dey & Molinaro, Mixed-integer quadratic programming is in NP, arXiv:1407.4798v1, p. 3, Proposition 4

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

open scoped Pointwise

/-- Proposition 4, p. 3 (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem proposition_4 :
    ∃ g : Polynomial ℕ, ∀ (p q m : ℕ) (A : Matrix (Fin m) (Fin (p + q)) ℚ) (b : Fin m → ℚ),
      ((polyhedron A b).Nonempty → IsPointedPoly A) →
      ∃ (N : ℕ) (mi : Fin N → ℕ) (Ai : (i : Fin N) → Matrix (Fin (mi i)) (Fin (p + q)) ℚ)
        (bi : (i : Fin N) → Fin (mi i) → ℚ) (KK : Finset (Finset (Fin (p + q) → ℤ))),
        {x | x ∈ polyhedron A b ∧ IsMixedInt p x} =
          (⋃ i, ⋃ R ∈ KK,
            polyhedron (Ai i) (bi i) + intCone ((fun r j => (r j : ℝ)) '' (R : Set (Fin (p + q) → ℤ)))) ∧
        (∀ i, Bornology.IsBounded (polyhedron (Ai i) (bi i)) ∧
          matSize (Ai i) + vecSize (bi i) ≤ g.eval (matSize A + vecSize b)) ∧
        (∀ R ∈ KK, ∀ r ∈ R, IsExtremeRayOf (recCone A) (fun j => (r j : ℝ)) ∧
          vecSize (fun j => (r j : ℚ)) ≤ g.eval (matSize A + vecSize b)) ∧
        (∀ R ∈ KK, LinearIndependent ℝ (fun r : R => fun j => ((r : Fin (p + q) → ℤ) j : ℝ))) := by sorry

end MIQPInNP.SmallSol
