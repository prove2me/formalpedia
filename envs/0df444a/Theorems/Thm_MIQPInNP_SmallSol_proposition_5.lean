-- Prove2me | Theorems.Thm_MIQPInNP_SmallSol_proposition_5
-- name    : MIQPInNP.SmallSol.proposition_5
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:43.102346+00:00
-- url     : https://prove2.me/theorems/2c9c607d-fb68-44e9-bf5d-22b67964a958
-- title:
--   Proposition 5, pp. 4–5 — a feasible mixed-integer linear system has a solution of polynomial bit-size (MIP is in NP)
-- statement:
--   Let $A\in\mathbb Q^{m\times n}$, $b\in\mathbb Q^m$ and $p\in\mathbb N$. There is a single polynomial $g$, fixed before $n$, $p$, $m$ and the data, such that: if the mixed-integer linear system
--   $$Ax\le b,\qquad x\in\mathbb Z^p\times\mathbb R^{n-p}$$
--   has a real solution, then it has a rational solution $\hat x$ with $\operatorname{size}(\hat x)\le g(\operatorname{size}[A\ b])$.
--
--   The paper states this as "the decision version of MIP is in NP" and justifies it by presenting a vertex of one of the polytopes $P_i$ of Proposition 4 as a certificate. The proof of Theorem 1 (Case 1, p. 7) uses exactly this: a point of the mixed-integer linear set of small complexity.
--
--   **Formalization Note** If $p>n$, all coordinates are required to be integers. The polynomial is quantified before all dimensions and data.
--
--   Differences from the source:
--   - reading: "the decision version of MIP is in NP" → every feasible mixed-integer linear system has a rational solution of bit-size at most $g(\operatorname{size}[A\ b])$; reason: Mathlib has no class NP; this is the certificate the paper presents on p. 5, and checking it is routine.
--   - encoding: "polynomial", "complexity" → `Polynomial ℕ` evaluated at Schrijver's bit-size; reason: polynomially equivalent to any standard encoding.
-- source:
--   Del Pia, Dey & Molinaro, Mixed-integer quadratic programming is in NP, arXiv:1407.4798v1, pp. 4–5, Proposition 5 and its justification

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

namespace MIQPInNP.SmallSol

/-- Proposition 5, pp. 4–5 (certificate form, p. 5) (Del Pia, Dey & Molinaro, arXiv:1407.4798v1). -/
theorem proposition_5 :
    ∃ g : Polynomial ℕ, ∀ (n p m : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
      (∃ x ∈ polyhedron A b, IsMixedInt p x) →
      ∃ xh : Fin n → ℚ, toReal xh ∈ polyhedron A b ∧ IsMixedInt p (toReal xh) ∧
        vecSize xh ≤ g.eval (matSize A + vecSize b) := by sorry

end MIQPInNP.SmallSol
