-- Prove2me | Theorems.Thm_Matrix_rank_map_le
-- name    : Matrix.rank_map_le
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-03T08:59:30.909384+00:00
-- url     : https://prove2.me/theorems/1edc2443-709a-4994-a5c7-6cbc845981b5
-- title:
--   The rank of a matrix does not increase under an entrywise field homomorphism
-- statement:
--   Let $F \subseteq F'$ be fields, more precisely let $\iota : F \to F'$ be a ring homomorphism of fields (necessarily injective), and let $A$ be a matrix with entries in $F$, with finitely many columns. Applying $\iota$ to every entry gives the matrix $\iota(A)$ with entries in $F'$. The statement asserts
--   $$\operatorname{rank}_{F'} \iota(A) \;\le\; \operatorname{rank}_F A.$$
--
--   Indeed the column space of $A$ over $F$ is spanned by $r = \operatorname{rank}_F A$ of its columns, and every column of $\iota(A)$ is the image of an $F$-linear combination of these, hence an $F'$-linear combination of their images; so the column space of $\iota(A)$ over $F'$ has dimension at most $r$. (Equality holds, but only the inequality is stated.)
--
--   **Use.** This transfers a rank bound obtained over a larger field back to the base field. In the reduction of `Leopoldt.exists_linearIndependent_log_conj_of_brumer`, the group matrix of $p$-adic logarithms has entries in a completion $K_{v_0}$ that need not contain the roots of unity needed for Dedekind's group determinant; the determinant argument (`Matrix.card_sub_one_le_rank_of_charSum_ne_zero`) is run after embedding into a completion $L_w$ of $L = K(\zeta_n)$, and this lemma brings the bound back to $K_{v_0}$.
--
--   **Formalization Note.** `Matrix.rank` is the dimension of the range of the linear map given by the matrix, over the field of its entries; it needs only `Fintype` on the column index, and the row index may be any type. `A.map ι` applies `ι` entrywise.
-- source:
--   Standard linear algebra: the column space of the image matrix is spanned by the images of a basis of the column space. Stated as an inequality $\operatorname{rank}_{F'}(\iota(A)) \le \operatorname{rank}_F(A)$ for a ring homomorphism $\iota : F \to F'$ of fields and `Matrix.rank` of Mathlib; equality holds but is not claimed.

import Mathlib

theorem Matrix.rank_map_le {m n : Type*} [Fintype n] {F F' : Type*} [Field F] [Field F']
    (ι : F →+* F') (A : Matrix m n F) : (A.map ι).rank ≤ A.rank := by sorry
