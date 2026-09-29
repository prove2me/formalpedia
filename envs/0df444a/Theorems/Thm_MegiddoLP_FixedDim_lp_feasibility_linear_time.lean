-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_lp_feasibility_linear_time
-- name    : MegiddoLP.FixedDim.lp_feasibility_linear_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:12:47.757982+00:00
-- url     : https://prove2.me/theorems/f020d465-0c13-41e6-9a63-7ed99c13a950
-- title:
--   Megiddo: LP feasibility in $d$ variables decided in $C(d)\cdot n$ steps on the real RAM
-- statement:
--   Fix the number of variables $d$. There are a program $R$ of the unit-cost real pointer machine (real RAM) and a constant $C=C(d)$ with the following property. For every number of constraints $n$ and every system
--
--   $$\sum_{j=1}^d a_{ij}x_j\ge b_i\qquad(i=1,\dots,n),$$
--
--   the machine $R$, started with the standard encoding of $(A,b)$ in memory (the numbers $n$ and $d$, then $A$ row by row, then $b$), halts within
--
--   $$C\cdot(n+1)$$
--
--   steps, and it accepts if and only if the system has a solution $x\in\mathbb{R}^d$.
--
--   This is Megiddo's theorem that linear programming in fixed dimension is solvable in linear time: "for every $d$ there exists a constant $C(d)$ such that $LP_1(n,d)<C(d)\cdot n$". It gives a strongly polynomial, indeed linear, algorithm for each fixed dimension. Deciding whether $\min\{c^Tx: Ax\ge b\}\le t$ is the same problem with the extra row $-c^Tx\ge-t$, so the decision form of optimization is covered.
--
--   **Formalization Note** The machine is `SmaleNinth.RAMProgram` (exact real arithmetic $+,-,\times,/$ at unit cost, a sign test, integer pointer registers, indirect memory access). The input convention is `SmaleNinth.encodeLP`, and time is the number of machine steps. The quantifier order is $\forall d\,\exists R\,\exists C\,\forall n,A,b$: the program and the constant depend on $d$ only. The paper's explicit bound $C(d)<2^{2^{d+2}}$ counts the paper's unspecified units of "effort" with an unquantified $\theta(nd)$ term, so it is not transferred to machine steps. The bound $C(n+1)$ rather than $Cn$ lets the machine halt when $n=0$. The case $d=0$ is included, and there the system is feasible iff every $b_i\le0$. Only acceptance or rejection is output, not an optimal solution.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, Abstract, p. 114 and §5, p. 126 (LP_1(n,d) < C(d)·n)

import Definitions.Def_Polyhedron
import Definitions.Def_SmaleNinth_BSSMachine
import Definitions.Def_SmaleNinth_RealRAM

/-!
Megiddo, *Linear programming in linear time when the dimension is fixed*, J. ACM 31 (1984),
Abstract p. 114 and §5 p. 126: for every fixed number `d` of variables, a linear program with
`n` constraints is solved in time `C(d)·n`. Decision form on the unit-cost real pointer
machine: a program depending only on `d` decides the feasibility of `Ax ≥ b`
(`A` of size `n × d`) within `C (n + 1)` steps on the standard input encoding `encodeLP`.
-/

open Matrix LinearOptimization SmaleNinth

namespace MegiddoLP.FixedDim

/-- **Megiddo (1984): fixed-dimension LP feasibility in linear time.** For every number `d`
of variables there are a program `R` of the real pointer machine and a constant `C` such that,
for every number `n` of constraints and every system `Ax ≥ b` with `A : ℝ^{n × d}`, `R` run on
`encodeLP A b` halts within `C (n + 1)` steps and accepts iff the system is feasible. -/
theorem lp_feasibility_linear_time (d : ℕ) :
    ∃ (R : RAMProgram) (C : ℕ),
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ),
        ∃ result : Bool,
          RAMDecidesInTime R (encodeLP A b) (C * (n + 1)) result ∧
          (result = true ↔ (polyhedron A b).Nonempty) := by sorry

end MegiddoLP.FixedDim
