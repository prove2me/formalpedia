-- Prove2me | Theorems.Thm_MinrankTW_relation_update_table
-- name    : MinrankTW.relation_update_table
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:13.715249+00:00
-- url     : https://prove2.me/theorems/3e0c35f3-7e7a-4cd9-bf41-2a03c7f23eb2
-- title:
--   Section 3.2 — the relation-update table for the five local operations
-- statement:
--   Let $M$ be a partial matrix whose interior consists of the rows $I_r$ and columns $I_c$ and whose bag consists of the rows $B_r$ and columns $B_c$, with interior and bag disjoint, and let $R=R(M)$ be its linear relation (13). Then:
--
--   1. introducing a row $i$ that is in neither the bag nor the interior and has no entries gives $\{(x,(y,0)) : (x,y)\in R\}$;
--   2. introducing a column $j$ that is in neither the bag nor the interior and has no entries gives $\{((x,v),y) : (x,y)\in R,\ v\in\mathbb F_q\}$;
--   3. assigning the value $\alpha$ to an entry $(i,j)$ with $i,j$ in the bag ($M'=M+\alpha E_{ij}$) gives $\{(x,y+\alpha x_je_i) : (x,y)\in R\}$;
--   4. forgetting a bag row $i$ (it moves to the interior) gives $\{(x,y_{-i}) : (x,y)\in R,\ y_i=0\}$;
--   5. forgetting a bag column $j$ gives $\{(x_{-j},y) : (x,y)\in R\}$.
--
--   These updates let the dynamic program carry the relation along a nice decomposition one entry or coordinate at a time.
--
--   **Formalization Note** Each clause is an equality of sets of pairs. In ambient coordinates appending a zero coordinate and deleting a coordinate set it to $0$, and appending a free coordinate $v$ sets it to $v$.
--
--   Differences from the source:
--   - encoding: bag and interior coordinates of a bag with a columns and c rows (F^a ⊕ F^c) → ambient coordinates in F^n × F^m supported on the bag (interior and bag disjoint); reason: the same relation with the bag coordinates embedded; same instances
--   - encoding: the operations of a nice decomposition (a new row/column is absent from the bag and the interior and carries no entry yet; the assigned entry has both indices in the bag) → these conditions as hypotheses of each clause; reason: they are the situation in which the table is applied; same instances
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.2, pp.10–11, Eq. (13) and the relation-update table

import Mathlib
import Definitions.Def_MinrankTW_relOfPartial

namespace MinrankTW

open Matrix

/-- **Section 3.2, the relation-update table**, Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), pp.10–11, with Eq. (13). Let `M` be a
partial matrix with interior rows `I_r`, interior columns `I_c`, bag rows `B_r` and bag columns
`B_c` (interior and bag disjoint), and `R = R(M)`. Then:
1. introducing a row `i` (in neither the bag nor the interior, with no entries) gives
   `{(x, (y, 0)) : (x, y) ∈ R}`;
2. introducing a column `j` (likewise) gives `{((x, v), y) : (x, y) ∈ R, v ∈ F}`;
3. assigning value `α` to entry `(i, j)` of the bag (`M′ = M + α E_ij`) gives
   `{(x, y + α x_j e_i) : (x, y) ∈ R}`;
4. forgetting bag row `i` (it moves to the interior) gives `{(x, y_{−i}) : (x, y) ∈ R, y_i = 0}`;
5. forgetting bag column `j` gives `{(x_{−j}, y) : (x, y) ∈ R}`.

**Formalization Note** Ambient coordinates (`relOfPartial`): appending a coordinate with value
`0` and deleting a coordinate are `Function.update · k 0`, appending a free coordinate is
`Function.update x j v`, `E_ij` is `Matrix.single i j` and `α x_j e_i` is
`Pi.single i (α * x j)`. Each clause is an equality of the underlying sets. -/
theorem relation_update_table {F : Type} [Field F] [Fintype F] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) F) (Ir Br : Finset (Fin m)) (Ic Bc : Finset (Fin n))
    (hr : Disjoint Ir Br) (hc : Disjoint Ic Bc) :
    (∀ i : Fin m, i ∉ Br → i ∉ Ir → (∀ j, M i j = 0) →
      (relOfPartial M Ir (insert i Br) Ic Bc : Set ((Fin n → F) × (Fin m → F))) =
        {p | ∃ x y, (x, y) ∈ relOfPartial M Ir Br Ic Bc ∧ p = (x, Function.update y i 0)}) ∧
    (∀ j : Fin n, j ∉ Bc → j ∉ Ic → (∀ i, M i j = 0) →
      (relOfPartial M Ir Br Ic (insert j Bc) : Set ((Fin n → F) × (Fin m → F))) =
        {p | ∃ x y, ∃ v : F, (x, y) ∈ relOfPartial M Ir Br Ic Bc ∧
          p = (Function.update x j v, y)}) ∧
    (∀ (i : Fin m) (j : Fin n) (α : F), i ∈ Br → j ∈ Bc →
      (relOfPartial (M + Matrix.single i j α) Ir Br Ic Bc : Set ((Fin n → F) × (Fin m → F))) =
        {p | ∃ x y, (x, y) ∈ relOfPartial M Ir Br Ic Bc ∧ p = (x, y + Pi.single i (α * x j))}) ∧
    (∀ i : Fin m, i ∈ Br →
      (relOfPartial M (insert i Ir) (Br.erase i) Ic Bc : Set ((Fin n → F) × (Fin m → F))) =
        {p | ∃ x y, (x, y) ∈ relOfPartial M Ir Br Ic Bc ∧ y i = 0 ∧
          p = (x, Function.update y i 0)}) ∧
    (∀ j : Fin n, j ∈ Bc →
      (relOfPartial M Ir Br (insert j Ic) (Bc.erase j) : Set ((Fin n → F) × (Fin m → F))) =
        {p | ∃ x y, (x, y) ∈ relOfPartial M Ir Br Ic Bc ∧ p = (Function.update x j 0, y)}) := by sorry

end MinrankTW
