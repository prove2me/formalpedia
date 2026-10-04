-- Prove2me | Theorems.Thm_MulticutLShaped_SimpleRecourse_eq25_equivalent
-- name    : MulticutLShaped.SimpleRecourse.eq25_equivalent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:03:28.282378+00:00
-- url     : https://prove2.me/theorems/fa04f0b0-2f7b-4e01-9744-b8c51e929b7f
-- title:
--   Section 5, Eqs. (24)-(25) — the simple recourse problem is equivalent to the LP (25)
-- statement:
--   Consider the simple recourse problem (3), (19)–(20) with first-stage set $K_1=\{x\mid Ax=b,\ x\ge0\}$, objective $z(x)=cx+\Psi(Tx)$, realizations $\xi_{ij}=(q^+_{ij},q^-_{ij},h_{ij})$ with probabilities $p_{ij}$ and $q_{ij}=q^+_{ij}+q^-_{ij}\ge 0$, and the LP (25)
--   $$
--   \min\ cx+\sum_{i,j}p_{ij}q^-_{ij}(\chi_i-h_{ij})+\sum_{i,j}u_{ij}\quad\text{s.t. } Ax=b,\ x\ge0,\ Tx-\chi=0,\ u_{ij}\ge p_{ij}q_{ij}(h_{ij}-\chi_i),\ u_{ij}\ge0 .
--   $$
--
--   1. For every $x\in K_1$, with $\chi=Tx$, the vector
--   $$
--   u^*_{ij}=\max\{0,\ p_{ij}q_{ij}(h_{ij}-T_ix)\}
--   $$
--   is feasible for (25) together with $(x,\chi)$, minimizes the objective of (25) over all $u$ feasible with $(x,\chi)$, and the minimum equals $z(x)=cx+\Psi(Tx)$.
--   2. Consequently, $x$ is optimal for (3) if and only if $(x,\chi,u)$ is optimal for (25) for some $\chi$ and $u$.
--
--   This is the equivalence the paper derives by introducing the slack $u_{ij}$ in (24), $p_{ij}q^-_{ij}(\chi_i-h_{ij})+u_{ij}=\theta_{ij}$, and substituting into (21)–(23). The multicut algorithm for simple recourse problems is a constraint-generation method for (25).
--
--   **Formalization Note.** The constraint $x\ge0$ of (3), omitted in the display of (25), is part of (25) here. $z(x)$ is an `EReal`; part 1 shows it is the real number given by (25).
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 389, Section 5, Eqs. (24), (25)

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

namespace MulticutLShaped.SimpleRecourse

variable {n1 m1 m2 J : ℕ}

/-- (24)–(25), p. 389: the simple recourse problem (3), (19)–(20) is equivalent to the LP (25).
For every `x ∈ K₁`, with `χ = Tx`, the choice `u_ij = max(0, p_ij q_ij (h_ij − χ_i))` is feasible
for (25), minimizes the (25) objective among all `u` feasible with `(x, χ)`, and the minimum equals
`cx + Ψ(Tx)`. Consequently `x` is optimal for (3) iff `(x, χ, u)` is optimal for (25) for some
`χ, u`. -/
theorem eq25_equivalent (inst : Instance n1 m1 m2 J) :
    (∀ x ∈ K1 inst,
      Feasible25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) ∧
      ((obj25 inst x (inst.T.mulVec x)
          (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i))) : ℝ)
          : EReal) = z inst x ∧
      ∀ u, Feasible25 inst x (inst.T.mulVec x) u →
        obj25 inst x (inst.T.mulVec x)
            (fun i j => max 0 (inst.p i j * inst.q i j * (inst.h i j - inst.T.mulVec x i)))
          ≤ obj25 inst x (inst.T.mulVec x) u) ∧
    ∀ x, IsOptimal inst x ↔ ∃ χ u, IsOptimal25 inst x χ u := by sorry

end MulticutLShaped.SimpleRecourse
