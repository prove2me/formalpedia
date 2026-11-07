-- Prove2me | Theorems.Thm_MinrankTW_rank_increment_table
-- name    : MinrankTW.rank_increment_table
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:31.006503+00:00
-- url     : https://prove2.me/theorems/48e16466-e75b-4d94-bd1a-aefba275757c
-- title:
--   Section 3.2 — the rank-increment table: $\delta\in\{0,1\}$ for each operation
-- statement:
--   Let $M$ be a partial matrix with interior rows $I_r$, interior columns $I_c$, bag rows $B_r$ and bag columns $B_c$ (interior and bag disjoint), interior block $A=M[I_r,I_c]$ and linear relation $R=R(M)$, and let $R'$ be the relation after the operation. The increase $\delta$ of the interior rank is:
--
--   1. $\delta=0$ when an entry of the bag is assigned (the interior block is unchanged), and likewise for introductions, which change neither the matrix nor the interior;
--   2. forgetting a bag row $i$: $\ \operatorname{rank}\begin{pmatrix}A\\V[i,:]\end{pmatrix}-\operatorname{rank}A=\dim R(0)-\dim R'(0)$;
--   3. forgetting a bag column $j$: $\ \operatorname{rank}\begin{pmatrix}A&U[:,j]\end{pmatrix}-\operatorname{rank}A=1+\dim\mathrm{dom}\,R'-\dim\mathrm{dom}\,R$;
--
--   and both increments in 2 and 3 belong to $\{0,1\}$.
--
--   Together with the relation updates this lets the dynamic program track the interior rank from the relation alone.
--
--   **Formalization Note** The block $\begin{pmatrix}A\\V[i,:]\end{pmatrix}$ is the interior block after row $i$ joins the interior, and $\begin{pmatrix}A&U[:,j]\end{pmatrix}$ the block after column $j$ does. Differences are stated in $\mathbb Z$; "belongs to $\{0,1\}$" is "equal or one more".
--
--   Differences from the source:
--   - encoding: bag and interior coordinates of a bag with a columns and c rows (F^a ⊕ F^c) → ambient coordinates in F^n × F^m supported on the bag (interior and bag disjoint); reason: the same relation with the bag coordinates embedded; same instances
--   - encoding: δ = 0 for introducing a row or a column → not a separate clause; reason: an introduction changes neither the matrix nor the interior, so both sides are literally the same interior rank
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.2, p.11, rank-increment table

import Mathlib
import Definitions.Def_MinrankTW_LinRel
import Definitions.Def_MinrankTW_relOfPartial
import Definitions.Def_MinrankTW_interiorRank

namespace MinrankTW

open Matrix

/-- **Section 3.2, the rank-increment table**, Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.11. For a partial matrix `M` with
interior `(I_r, I_c)` and bag `(B_r, B_c)` (disjoint), interior block `A = M[I_r, I_c]` and
`R = R(M)`:
1. assigning an entry of the bag leaves the interior block unchanged, so `δ = 0` (introductions
   do not change `M` or the interior at all);
2. forgetting bag row `i`: `rank [A; V[i, :]] − rank A = dim R(0) − dim R′(0)`, where `R′` is the
   relation after the operation;
3. forgetting bag column `j`: `rank [A U[:, j]] − rank A = 1 + dim dom R′ − dim dom R`;
and both increments belong to `{0, 1}`.

**Formalization Note** `rank [A; V[i, :]]` is the interior rank with `i` added to the interior
rows, `rank [A U[:, j]]` the interior rank with `j` added to the interior columns; `R′` is
`relOfPartial` for the new interior and bag. The differences are stated in `ℤ`, and
membership in `{0, 1}` as "equal or one more". -/
theorem rank_increment_table {F : Type} [Field F] [Fintype F] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) F) (Ir Br : Finset (Fin m)) (Ic Bc : Finset (Fin n))
    (hr : Disjoint Ir Br) (hc : Disjoint Ic Bc) :
    (∀ (i : Fin m) (j : Fin n) (α : F), i ∈ Br → j ∈ Bc →
      interiorRank (M + Matrix.single i j α) Ir Ic = interiorRank M Ir Ic) ∧
    (∀ i : Fin m, i ∈ Br →
      ((interiorRank M (insert i Ir) Ic : ℤ) - interiorRank M Ir Ic =
        (Module.finrank F (relZero (relOfPartial M Ir Br Ic Bc)) : ℤ) -
          Module.finrank F (relZero (relOfPartial M (insert i Ir) (Br.erase i) Ic Bc))) ∧
      (interiorRank M (insert i Ir) Ic = interiorRank M Ir Ic ∨
        interiorRank M (insert i Ir) Ic = interiorRank M Ir Ic + 1)) ∧
    (∀ j : Fin n, j ∈ Bc →
      ((interiorRank M Ir (insert j Ic) : ℤ) - interiorRank M Ir Ic =
        1 + (Module.finrank F (relDom (relOfPartial M Ir Br (insert j Ic) (Bc.erase j))) : ℤ) -
          Module.finrank F (relDom (relOfPartial M Ir Br Ic Bc))) ∧
      (interiorRank M Ir (insert j Ic) = interiorRank M Ir Ic ∨
        interiorRank M Ir (insert j Ic) = interiorRank M Ir Ic + 1)) := by sorry

end MinrankTW
