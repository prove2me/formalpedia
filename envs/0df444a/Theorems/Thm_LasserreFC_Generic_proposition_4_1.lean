-- Prove2me | Theorems.Thm_LasserreFC_Generic_proposition_4_1
-- name    : LasserreFC.Generic.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:45.327006+00:00
-- url     : https://prove2.me/theorems/d8805dd0-4368-4fe8-bb3c-7f4cea8305c2
-- title:
--   Proposition 4.1, p. 11 — a polynomial ℛ in the coefficients vanishes exactly when the homogenised system (4.5) is solvable
-- statement:
--   Let $k\le n$ and let $d_0,\dots,d_k,d_{k+1}$ be nonnegative integers. There is a real polynomial $\mathscr R$ in the coefficients of tuples $(p_0,\dots,p_k,q)\in\mathbb R[x]_{d_0}\times\cdots\times\mathbb R[x]_{d_k}\times\mathbb R[x]_{d_{k+1}}$ such that for every such tuple:
--   1. the system (4.5),
--   $$\operatorname{rank}\big[\nabla_x\tilde p_0(\tilde x)\ \cdots\ \nabla_x\tilde p_k(\tilde x)\big]\le k,\qquad\tilde p_1(\tilde x)=\cdots=\tilde p_k(\tilde x)=\tilde q(\tilde x)=0,$$
--   has a solution $0\neq\tilde x\in\mathbb C^{n+1}$ if and only if $\mathscr R(p_0,\dots,p_k;q)=0$;
--   2. in particular, if $\mathscr R(p_0,\dots,p_k;q)\neq0$, then the affine system (4.4) has no solution in $\mathbb C^n$.
--
--   Here $\tilde p$ is the homogenisation of $p$ at its nominal degree. The proposition turns the condition "the KKT variety of $\min p_0$ s.t. $p_1=\cdots=p_k=0$ meets the hypersurface $q=0$" into the vanishing of one polynomial in the input coefficients; it is the source of item (c) of Condition 4.3.
--
--   **Formalization Note** The page defines $\mathscr R$ by (4.6) as $\sum_i\mathscr R_i^2$ for the elimination polynomials of Theorem 2.5; the statement asserts the existence of a polynomial with the stated property, which is all the proposition says about $\mathscr R$. The tuple is indexed by $\{0,\dots,k+1\}$, with entry $k+1$ the polynomial $q$.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 11, Proposition 4.1 (with (4.4)–(4.6), pp. 10–11)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Homog

namespace LasserreFC.Generic

open MvPolynomial

/-- Proposition 4.1, p. 11. For `k ≤ n` and nominal degrees `d₀, …, d_{k+1}` there is a real
polynomial `ℛ` in the coefficients of `(p₀, …, p_k, q) ∈ ℝ[x]_{d₀} × ⋯ × ℝ[x]_{d_k} × ℝ[x]_{d_{k+1}}`
such that, for every such tuple, (4.5) has a solution `0 ≠ x̃ ∈ ℂ^{n+1}` iff `ℛ(p₀, …, p_k; q) = 0`;
in particular, if `ℛ(p₀, …, p_k; q) ≠ 0` then (4.4) has no solution in `ℂⁿ`.
The tuple is `P : Fin (k + 2) → ℝ[x]`: `P 0 = p₀`, `P (i + 1) = p_{i+1}` (`i < k`),
`P (k + 1) = q`. -/
theorem proposition_4_1 {n k : ℕ} (hk : k ≤ n) (d : Fin (k + 2) → ℕ) :
    ∃ R : MvPolynomial (Fin (k + 2) × (Fin n →₀ ℕ)) ℝ,
      ∀ P : Fin (k + 2) → MvPolynomial (Fin n) ℝ, (∀ i, (P i).totalDegree ≤ d i) →
        ((MvPolynomial.eval (tupleCoeffs P) R = 0 ↔
            Sys45 (d 0) (P 0) (fun i : Fin k => d i.succ.castSucc)
              (fun i : Fin k => P i.succ.castSucc) (d (Fin.last (k + 1))) (P (Fin.last (k + 1)))) ∧
          (MvPolynomial.eval (tupleCoeffs P) R ≠ 0 →
            ¬ Sys44 (P 0) (fun i : Fin k => P i.succ.castSucc) (P (Fin.last (k + 1))))) := by sorry

end LasserreFC.Generic
