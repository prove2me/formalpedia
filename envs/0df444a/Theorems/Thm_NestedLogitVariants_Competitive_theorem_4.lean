-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_theorem_4
-- name    : NestedLogitVariants.Competitive.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:23:19.556133+00:00
-- url     : https://prove2.me/theorems/352bb180-32cc-4c88-adf2-bbea3d1f539a
-- title:
--   Theorem 4, p. 15 — with γ_i ≤ 1 and v_i0 = 0, some optimal assortment has S_i* = N_ij in every nest
-- statement:
--   Consider the nested logit assortment problem (2) in which every nest is fully captured, $v_{i0} = 0$ for all $i \in M$, and every dissimilarity parameter satisfies $\gamma_i \le 1$. Products in each nest are ordered by revenue, $r_{i1} \ge \dots \ge r_{in}$, and $N_{ij} = \{1, \dots, j\}$ denotes the nested-by-revenue assortment of the $j$ highest-revenue products of nest $i$, with $N_{i0} = \emptyset$ and $N_+ = \{0, 1, \dots, n\}$. Then there exists an optimal solution $(S^*_1, \dots, S^*_m)$ to problem (2) such that
--
--   $$S^*_i = N_{ij} \quad \text{for some } j \in N_+, \qquad \text{for all } i \in M.$$
--
--   This is the main structural result of the paper for competitive products and fully-captured nests: the search for an optimal assortment can be restricted to the $(n+1)^m$ combinations of nested-by-revenue assortments, and the paper then finds the best combination with a linear program with $1 + m$ variables.
--
--   **Formalization Note** The standing assumptions of §3 (p. 13), $\gamma_i \le 1$ and $v_{i0} = 0$, are hypotheses, together with those of §1 and the pins of the model definition ($v_{ij} > 0$, $r_{ij} \ge 0$, $\gamma_i > 0$, revenues ordered). The no-nest weight is only assumed nonnegative, $v_0 \ge 0$: the section assumes $v_0 > 0$ "without loss of generality", and the case $v_0 = 0$ is covered by the paper's remark that offering the single highest-revenue product is then optimal. Products are indexed $0, \dots, n-1$ and $N_{ij}$ is `nbr n j` $= \{k : k < j\}$ with $j \le n$; $j = 0$ gives the empty assortment. The statement asserts that *some* optimal assortment is nested by revenue, not that every optimal assortment is (which fails under ties).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 15, Theorem 4

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- Theorem 4, p. 15: with `γ_i ≤ 1` and `v_{i0} = 0` for all nests, there exists an optimal
solution `(S*_1, …, S*_m)` to problem (2) such that, for all `i ∈ M`, `S*_i = N_ij` for some
`j ∈ N_+ = {0, 1, …, n}`. -/
theorem theorem_4 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (hfc : ∀ i, I.vnp i = 0) :
    ∃ S : ι → Finset (Fin n), IsOptimal I S ∧ ∀ i, ∃ j ≤ n, S i = nbr n j := by sorry

end NestedLogitVariants.Competitive
