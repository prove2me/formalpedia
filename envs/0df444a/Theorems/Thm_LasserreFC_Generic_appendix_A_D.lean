-- Prove2me | Theorems.Thm_LasserreFC_Generic_appendix_A_D
-- name    : LasserreFC.Generic.appendix_A_D
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:23.659005+00:00
-- url     : https://prove2.me/theorems/e53d28d3-69c7-40a6-a81c-967b39482124
-- title:
--   Appendix A, pp. 19–20 — 𝒟 does not vanish identically: some admissible (p₀, …, p_k) makes (4.10) unsolvable
-- statement:
--   Let $k\le n$ and let $d_0,\dots,d_k$ be positive integers. There exist $p_i\in\mathbb R[x]_{d_i}$ ($i=0,\dots,k$) for which the system (4.10),
--   $$\operatorname{rank}\widetilde P(\tilde x,y)\le 2k,\qquad\tilde p_1(\tilde x)=\cdots=\tilde p_k(\tilde x)=0,\qquad(\nabla_x\tilde p_1)^Ty=\cdots=(\nabla_x\tilde p_k)^Ty=0,$$
--   has no complex solution $(\tilde x,y)$ with $\tilde x\neq0$, $y\neq0$.
--
--   By Proposition 4.2 this says that the polynomial $\mathscr D(p_0,\dots,p_k)$ of (4.11) does not vanish identically on $\mathbb R[x]_{d_0}\times\cdots\times\mathbb R[x]_{d_k}$, so item (d) of Condition 4.3 holds on a nonempty Zariski open set of inputs.
--
--   **Formalization Note** The statement is the unsolvability form the Appendix reduces to; it does not mention $\mathscr D$.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, pp. 19–20, Appendix A (second part)

import Mathlib
import Definitions.Def_LasserreFC_Generic_Homog

namespace LasserreFC.Generic

/-- Appendix A, pp. 19–20: `𝒟` does not vanish identically. For `k ≤ n` and positive degrees
`d₀, …, d_k` there are `pᵢ ∈ ℝ[x]_{dᵢ}` (`i = 0, …, k`) for which (4.10) has no complex solution
`(x̃, y)` with `x̃ ≠ 0`, `y ≠ 0` (by Proposition 4.2, `𝒟(p₀, …, p_k) ≠ 0`).
The tuple is `P : Fin (k + 1) → ℝ[x]` as in Proposition 4.2. -/
theorem appendix_A_D {n k : ℕ} (hk : k ≤ n) (d : Fin (k + 1) → ℕ) (hd : ∀ i, 0 < d i) :
    ∃ P : Fin (k + 1) → MvPolynomial (Fin n) ℝ, (∀ i, (P i).totalDegree ≤ d i) ∧
      ¬ Sys410 (d 0) (P 0) (fun i : Fin k => d i.succ) (fun i : Fin k => P i.succ) := by sorry

end LasserreFC.Generic
