-- Prove2me | Theorems.Thm_LostSalesOldNew_StateReduction_vectorBaseStock_mem_Zs
-- name    : LostSalesOldNew.StateReduction.vectorBaseStock_mem_Zs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:30.333389+00:00
-- url     : https://prove2.me/theorems/c1494205-f507-45f6-9836-2c82afd44adb
-- title:
--   (5) and §4 — every vector base-stock policy with level vector s lies in Z(s)
-- statement:
--   Let $L\ge 1$ be the lead time and let $s=(s_0,\dots,s_L)$ satisfy $s_0\ge s_1\ge\dots\ge s_L\ge 0$. Let $z_s$ be the vector base-stock policy with parameter $s$,
--   $$
--   z_s(x) = \Bigl[\min\{s_l - v_l,\ l=0,\dots,L\}\Bigr]^+, \qquad v_l=\sum_{m=l}^{L-1}x_m,\ v_L=0 .
--   $$
--   Then $z_s\in Z(s)$: it orders a nonnegative amount in every state $x\ge 0$, it orders nothing in every state $x\ge 0$ outside $X(s)$, and $v_l+z_s(x)\le s_l$ for $l=0,\dots,L$ and every $x\in X(s)$.
--
--   The paper states this for Morton's standard vector $\bar s$ ("the standard vector base-stock policy [is in $Z(\bar s)$], by construction"); the construction gives it for every level vector, which is what is stated here. The same sentence of the paper also asserts that any optimal policy lies in $Z(\bar s)$; that part rests on Morton's bounds (4), which the paper cites without proof, and it is not part of this statement.
--
--   The result shows that $Z(s)$ contains the paper's vector base-stock heuristics, so Claim 1 applies to them.
--
--   **Formalization Note.** The paper assumes $L>0$. Policies are functions `(Fin L → ℝ) → ℝ`; $Z(s)$ quantifies its sign and zero conditions over nonnegative states only.
-- source:
--   Zipkin, Old and New Methods for Lost-Sales Inventory Systems, Operations Research 56(5) (2008), (5) and the definition of vector base-stock policies, p. 1258; §4, p. 1259

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model

namespace LostSalesOldNew.StateReduction

theorem vectorBaseStock_mem_Zs {L : ℕ} (hL : 0 < L)
    (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s) :
    vectorBaseStock s ∈ Zs s := by sorry

end LostSalesOldNew.StateReduction
