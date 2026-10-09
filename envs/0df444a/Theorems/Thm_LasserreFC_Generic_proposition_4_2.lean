-- Prove2me | Theorems.Thm_LasserreFC_Generic_proposition_4_2
-- name    : LasserreFC.Generic.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:27.338387+00:00
-- url     : https://prove2.me/theorems/ec83bd1f-e214-41d9-bc68-25231e677f58
-- title:
--   Proposition 4.2, p. 12 — a polynomial 𝒟 in the coefficients vanishes exactly when (4.10) is solvable; 𝒟 ≠ 0 makes the KKT system nonsingular
-- statement:
--   Let $k\le n$ and let $d_0,\dots,d_k$ be nonnegative integers. There is a real polynomial $\mathscr D$ in the coefficients of tuples $(p_0,\dots,p_k)\in\mathbb R[x]_{d_0}\times\cdots\times\mathbb R[x]_{d_k}$ such that for every such tuple:
--   1. the system (4.10),
--   $$\operatorname{rank}\widetilde P(\tilde x,y)\le 2k,\qquad \tilde p_1(\tilde x)=\cdots=\tilde p_k(\tilde x)=0,\qquad(\nabla_x\tilde p_1)^Ty=\cdots=(\nabla_x\tilde p_k)^Ty=0,$$
--   has a solution $(\tilde x,y)\in\mathbb C^{n+1}\times\mathbb C^n$ with $\tilde x\neq0$, $y\neq0$ if and only if $\mathscr D(p_0,\dots,p_k)=0$;
--   2. in particular, if $\mathscr D(p_0,\dots,p_k)\neq0$, then the KKT system (4.2) of $\min p_0$ s.t. $p_1=\cdots=p_k=0$ is nonsingular: the matrix $H_p(x,\lambda)$ is nonsingular at every critical pair $(x,\lambda)$.
--
--   The proposition is the source of item (d) of Condition 4.3, which yields the nonsingularity of $H(u)$ at critical points of (1.1).
--
--   **Formalization Note** As for Proposition 4.1, $\mathscr D$ (defined on the page by (4.11)) enters existentially. Nonsingularity is asserted at every complex critical pair $(x,\lambda)\in\mathbb C^n\times\mathbb C^k$, which contains the real ones used later.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 12, Proposition 4.2 (with (4.2), H_p(x, λ), (4.10), (4.11), pp. 10–12)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Homog

namespace LasserreFC.Generic

open MvPolynomial

/-- Proposition 4.2, p. 12. For `k ≤ n` and nominal degrees `d₀, …, d_k` there is a real
polynomial `𝒟` in the coefficients of `(p₀, …, p_k) ∈ ℝ[x]_{d₀} × ⋯ × ℝ[x]_{d_k}` such that, for
every such tuple, (4.10) has a solution `(x̃, y) ∈ ℂ^{n+1} × ℂⁿ` with `x̃ ≠ 0`, `y ≠ 0` iff
`𝒟(p₀, …, p_k) = 0`; in particular, if `𝒟(p₀, …, p_k) ≠ 0` then the KKT system (4.2) is
nonsingular (at every complex critical pair). The tuple is `P : Fin (k + 1) → ℝ[x]`,
`P i = pᵢ`. -/
theorem proposition_4_2 {n k : ℕ} (hk : k ≤ n) (d : Fin (k + 1) → ℕ) :
    ∃ Dp : MvPolynomial (Fin (k + 1) × (Fin n →₀ ℕ)) ℝ,
      ∀ P : Fin (k + 1) → MvPolynomial (Fin n) ℝ, (∀ i, (P i).totalDegree ≤ d i) →
        ((MvPolynomial.eval (tupleCoeffs P) Dp = 0 ↔
            Sys410 (d 0) (P 0) (fun i : Fin k => d i.succ) (fun i : Fin k => P i.succ)) ∧
          (MvPolynomial.eval (tupleCoeffs P) Dp ≠ 0 →
            KKTNonsingular (P 0) (fun i : Fin k => P i.succ))) := by sorry

end LasserreFC.Generic
