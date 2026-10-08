-- Prove2me | Theorems.Thm_ManneJobShop_Formulation_card_conflicts_uniform
-- name    : ManneJobShop.Formulation.card_conflicts_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:09:34.817983+00:00
-- url     : https://prove2.me/theorems/4502fab0-1a7e-47a3-a1fe-4d218e23ac6e
-- title:
--   pp. 221–222 — with M machines of p tasks each, n = Mp and there are M·p(p − 1)/2 conflicting pairs
-- statement:
--   Fix a job-shop instance with $n$ tasks and $M$ machines, and suppose that every machine is required by exactly $p$ tasks. Then
--   $$n=Mp\qquad\text{and}\qquad m=|\mathcal C|=M\cdot\frac{p(p-1)}{2},$$
--   where $\mathcal C$ is the set of conflicting pairs $(j,k)$, $j<k$, of tasks on the same machine. Since the integer program has one variable $x_j$ per task and one $y_{jk}$ per conflicting pair, it has $n+m$ integer unknowns; for $M=5$ and $p=10$ this is $50+225=275$, the count on p. 222.
--
--   This measures the size of Manne's formulation, which he compares with other proposals of the time.
--
--   **Formalization Note** Natural-number division $p(p-1)/2$ is exact because $p(p-1)$ is even, and the expression is $0$ for $p=0$. The numerical instance $275$ is given here in prose only; the statement is the general count.
-- source:
--   Manne, On the Job-Shop Scheduling Problem, Operations Research 8 (1960), pp. 221–222, Computational Aspects, "If, then, there are n tasks and if also there are m possible conflicting pairs of machine assignments"

import Mathlib
import Definitions.Def_ManneJobShop_Formulation_Model

namespace ManneJobShop.Formulation

/-- Manne (1960), pp. 221–222: if every one of the `M` machines carries exactly `p` tasks, then
there are `n = M p` tasks and `m = M · p(p - 1)/2` conflicting pairs, i.e. `n + m` unknowns
`x_j, y_jk` (for 5 machines and 10 tasks each: 50 + 225 = 275). -/
theorem card_conflicts_uniform {n : ℕ} (I : Instance n) (p : ℕ)
    (hp : ∀ i : Fin I.M, (Finset.univ.filter (fun j : Fin n => I.mach j = i)).card = p) :
    n = I.M * p ∧ (conflicts I).card = I.M * (p * (p - 1) / 2) := by sorry

end ManneJobShop.Formulation
