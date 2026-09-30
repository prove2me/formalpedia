-- Prove2me | Theorems.Thm_Lubbecke2005_RyanFoster_branching_dichotomy
-- name    : Lubbecke2005.RyanFoster.branching_dichotomy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T15:36:48.953757+00:00
-- url     : https://prove2.me/theorems/72486757-b697-4a96-87af-899bd7c2b7d3
-- title:
--   §7.3 — every $0/1$ solution of $A\lambda = \mathbf 1$ lies in one of the two Ryan–Foster branches
-- statement:
--   Let $A = (a_{rj}) \in \{0,1\}^{m \times |J'|}$ be a $0/1$ matrix and let $\lambda \in \{0,1\}^{|J'|}$ be a $0/1$ vector with $A\lambda = \mathbf 1$, i.e. an integer solution of the set-partitioning system: every row is covered by exactly one selected column. Then for every pair of rows $r, s \in \{1, \dots, m\}$,
--
--   $$\sum_{j \in J'} a_{rj}\, a_{sj}\, \lambda_j = 0 \quad\text{or}\quad \sum_{j \in J'} a_{rj}\, a_{sj}\, \lambda_j = 1 .$$
--
--   The paper describes Ryan–Foster branching on a pair of rows as the two branches "$\sum_{j\in J'} a_{rj}a_{sj}\lambda_j = 1$" (the rows are covered by the same column) and "$\sum_{j\in J'} a_{rj}a_{sj}\lambda_j = 0$" (they are covered by two distinct columns), and requires of a valid branching scheme that "integer solutions remain intact" (p. 1019). This statement is that requirement for the Ryan–Foster branches: no integer solution is lost. Together with Proposition 3, which says that a fractional basic solution violates both branches for some pair of rows, it expresses the validity of the scheme.
--
--   **Formalization Note** The paper states the two branches and the validity requirement in prose; this theorem reads them as the dichotomy above for all $0/1$ solutions of $A\lambda = \mathbf 1$ (nonnegativity is implied by the $0/1$ property). The case $r = s$ is included. The statement "this information can be easily transferred to and obeyed by the pricing problem" is not formalized. Rows are `Fin m`, columns `Fin n`, and the quantity is `pairCover A lam r s`.
-- source:
--   Lübbecke and Desrosiers, Selected Topics in Column Generation, Operations Research 53(6), 2005, p. 1020, §7.3, paragraph after Proposition 3 (with the validity requirement of §7.3, p. 1019)

import Mathlib
import Definitions.Def_Lubbecke2005_RyanFoster_SetPartitioning

open Matrix

namespace Lubbecke2005.RyanFoster

/-- **Ryan–Foster branching keeps every integer solution** (Lübbecke–Desrosiers 2005,
§7.3, p. 1020, the paragraph after Proposition 3, with "integer solutions remain intact",
p. 1019). If `A` is a `0/1` matrix and `λ ∈ {0, 1}^{|J′|}` satisfies `Aλ = 𝟏`, then for
every pair of rows `r, s` the quantity `∑_j a_rj a_sj λ_j` is `1` (the rows are covered by
the same column) or `0` (they are covered by two distinct columns). -/
theorem branching_dichotomy {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : IsZeroOneMatrix A) (lam : Fin n → ℝ) (hint : IsZeroOneVector lam)
    (hfeas : A *ᵥ lam = fun _ => 1) (r s : Fin m) :
    pairCover A lam r s = 0 ∨ pairCover A lam r s = 1 := by sorry

end Lubbecke2005.RyanFoster
