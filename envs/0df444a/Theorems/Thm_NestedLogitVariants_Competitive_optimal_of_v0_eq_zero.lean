-- Prove2me | Theorems.Thm_NestedLogitVariants_Competitive_optimal_of_v0_eq_zero
-- name    : NestedLogitVariants.Competitive.optimal_of_v0_eq_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T07:22:15.940998+00:00
-- url     : https://prove2.me/theorems/0310ddf5-c563-4057-9360-8d45d51efa6e
-- title:
--   §3, p. 14 — with v_0 = 0 and v_i0 = 0, offering only the highest-revenue product over all nests is optimal
-- statement:
--   Consider the nested logit assortment problem (2) in which no customer leaves without considering a nest, $v_0 = 0$, and every nest is fully captured, $v_{i0} = 0$ for all nests $i \in M$. Products in each nest are ordered by revenue, $r_{i1} \ge r_{i2} \ge \dots \ge r_{in}$, and $n \ge 1$. Let $i \in M$ be a nest whose top product has the largest revenue over all nests, $r_{i1} = \max_{l \in M} r_{l1}$. Then the assortment that offers only product $1$ in nest $i$ and nothing in any other nest,
--
--   $$S_i = N_{i1} = \{1\}, \qquad S_l = \emptyset \quad (l \ne i),$$
--
--   is an optimal solution to problem (2).
--
--   This is the case that §3 sets aside with its "without loss of generality $v_0 > 0$": in it, the conclusion of Theorem 4 holds directly, since the optimal assortment above is nested by revenue in every nest.
--
--   **Formalization Note** Products are indexed $0, \dots, n-1$, so the paper's product $1$ is index $0$ and $N_{i1}$ is `nbr n 1`. The hypothesis $\gamma_i \le 1$ of §3 is not needed and is omitted, which makes the statement stronger. The paper's further remark that this product "would be purchased with probability one" is not stated. Standing assumptions and pins as in the model definition.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 14, §3 (paragraph before Proposition 2)

import Mathlib
import Definitions.Def_NestedLogitVariants_Competitive_Model

namespace NestedLogitVariants.Competitive

/-- §3, p. 14 (the case `v_0 = 0` set aside by the section's "without loss of generality"):
when `v_0 = 0` and `v_{i0} = 0` for every nest, offering only the product with the largest revenue
`max_{l ∈ M} r_{l1}` (here product `0` of nest `i`) and nothing in the other nests is optimal. -/
theorem optimal_of_v0_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n) (hI : I.Standing)
    (hfc : ∀ i, I.vnp i = 0) (hv0 : I.v0 = 0) (hn : 0 < n) (i : ι)
    (hi : ∀ l, I.r l ⟨0, hn⟩ ≤ I.r i ⟨0, hn⟩) :
    IsOptimal I (fun l => if l = i then nbr n 1 else ∅) := by sorry

end NestedLogitVariants.Competitive
