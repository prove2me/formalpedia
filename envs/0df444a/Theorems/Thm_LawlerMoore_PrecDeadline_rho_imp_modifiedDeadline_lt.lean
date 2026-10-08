-- Prove2me | Theorems.Thm_LawlerMoore_PrecDeadline_rho_imp_modifiedDeadline_lt
-- name    : LawlerMoore.PrecDeadline.rho_imp_modifiedDeadline_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:27:17.286251+00:00
-- url     : https://prove2.me/theorems/9a667101-e0b7-4c25-bbc8-f92ed445f55c
-- title:
--   Section 2 — $i\rho j$ implies $\bar d_i < \bar d_j$
-- statement:
--   Let $n$ jobs carry real deadlines $d_1,\dots,d_n$, and let $\rho$ be a transitive precedence relation on them ($i\rho j$: job $i$ must precede job $j$). Assume the jobs are numbered so that $i\rho j$ implies $i \le j$. Let $\varepsilon > 0$ and let $\bar d_j = \min\{d_k \mid k = j \text{ or } j\rho k\} + j\varepsilon$ be the modified deadlines. Then for any two distinct jobs $i \neq j$,
--
--   $$
--   i\rho j \;\Longrightarrow\; \bar d_i < \bar d_j .
--   $$
--
--   So ordering jobs by increasing modified deadline never places a job before one of its required predecessors; this is what makes the sequence of the §2 Theorem consistent with the precedence constraints.
--
--   **Formalization Note** The paper's relation is a partial order, hence reflexive; "$i\rho j$" in this sentence means that $i$ must precede $j$, so the statement is made for $i \ne j$ (for $i = j$ it would read $\bar d_i < \bar d_i$). Only transitivity, the numbering and $\varepsilon > 0$ are used, so only these are assumed; the paper's "$\varepsilon$ is a small number" is read as $\varepsilon > 0$ here (smallness is not needed for this claim). Jobs are `Fin n`, 0-based.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 78, Section 2

import Mathlib
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline

namespace LawlerMoore.PrecDeadline

theorem rho_imp_modifiedDeadline_lt (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ i j, i ≠ j → ρ i j → modifiedDeadline ρ d ε i < modifiedDeadline ρ d ε j := by sorry

end LawlerMoore.PrecDeadline
