-- Prove2me | Theorems.Thm_LasserreFC_Generic_appendix_A_R
-- name    : LasserreFC.Generic.appendix_A_R
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:29.212467+00:00
-- url     : https://prove2.me/theorems/4bd34693-49a7-48b2-b953-523b61bd0468
-- title:
--   Appendix A, pp. 18–19 — ℛ does not vanish identically: some admissible (p₀, …, p_k, q) makes (4.5) unsolvable
-- statement:
--   Let $k\le n$ and let $d_0,\dots,d_k,d_{k+1}$ be positive integers. There exist $p_0\in\mathbb R[x]_{d_0},\dots,p_k\in\mathbb R[x]_{d_k}$ and $q\in\mathbb R[x]_{d_{k+1}}$ for which the system (4.5),
--   $$\operatorname{rank}\big[\nabla_x\tilde p_0(\tilde x)\ \cdots\ \nabla_x\tilde p_k(\tilde x)\big]\le k,\qquad \tilde p_1(\tilde x)=\cdots=\tilde p_k(\tilde x)=\tilde q(\tilde x)=0,$$
--   has no solution $0\neq\tilde x\in\mathbb C^{n+1}$.
--
--   By Proposition 4.1 this says that the polynomial $\mathscr R(p_0,\dots,p_k;q)$ of (4.6) does not vanish identically on $\mathbb R[x]_{d_0}\times\cdots\times\mathbb R[x]_{d_{k+1}}$, so item (c) of Condition 4.3 holds on a nonempty Zariski open set of inputs.
--
--   **Formalization Note** The statement is the unsolvability form the Appendix reduces to ("By Proposition 4.1, it is enough to show…"); it does not mention $\mathscr R$.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, pp. 18–19, Appendix A (first part)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Homog

namespace LasserreFC.Generic

/-- Appendix A, pp. 18–19: `ℛ` does not vanish identically. For `k ≤ n` and positive degrees
`d₀, …, d_{k+1}` there are `p₀ ∈ ℝ[x]_{d₀}, …, p_k ∈ ℝ[x]_{d_k}, q ∈ ℝ[x]_{d_{k+1}}` for which
the system (4.5) has no solution `0 ≠ x̃ ∈ ℂ^{n+1}` (by Proposition 4.1, `ℛ(p₀, …, p_k; q) ≠ 0`).
The tuple is `P : Fin (k + 2) → ℝ[x]` as in Proposition 4.1. -/
theorem appendix_A_R {n k : ℕ} (hk : k ≤ n) (d : Fin (k + 2) → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ P : Fin (k + 2) → MvPolynomial (Fin n) ℝ, (∀ i, (P i).totalDegree ≤ d i) ∧
      ¬ Sys45 (d 0) (P 0) (fun i : Fin k => d i.succ.castSucc)
          (fun i : Fin k => P i.succ.castSucc) (d (Fin.last (k + 1))) (P (Fin.last (k + 1))) := by sorry

end LasserreFC.Generic
