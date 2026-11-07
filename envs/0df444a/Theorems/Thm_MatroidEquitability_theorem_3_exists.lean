-- Prove2me | Theorems.Thm_MatroidEquitability_theorem_3_exists
-- name    : MatroidEquitability.theorem_3_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:35.830453+00:00
-- url     : https://prove2.me/theorems/2f288fcb-5a2a-4a69-851b-76e147bf4f35
-- title:
--   Theorem 3, existence clause (the sentence on polynomial time is not stated) — exchange theorem of Akrami, Liu, Raj, Végh
-- statement:
--   Let $B,D$ be disjoint bases of a finite matroid $M=(E,\mathcal I)$ and let $S\subseteq E$. If
--
--   $$
--   |B\cap S|>|D\cap S|,
--   $$
--
--   then there exist $t\in D\setminus S$ and a $(t,S)$-exchangeable set for $B$ and $D$.
--
--   This exchange theorem is the combinatorial input of the proof of the main theorem; the paper imports it from Akrami, Liu, Raj and Végh, *Matroids are equitable*, Combinatorica 46(3), 2026, Theorem 1.4.
--
--   **Scope of this item.** This item formalizes the first sentence of the printed Theorem 3. The printed theorem continues "Moreover, such a set can be found in polynomial time." That second sentence is not stated here: the proof of the mission's goal uses only existence, and the running-time claim would need an oracle machine model.
--
--   Differences from the source:
--   - encoding: a matroid, with weights summed over sets and maxima over $E$, never called finite on the page → `Matroid α` with `[M.Finite]`, sums as `finsum`; reason: the sums, $\max_{e\in E}$ and "finitely many partitions" all presuppose a finite ground set; the same instances
--   - reading: the definition of exchangeable set takes $S\subseteq B\cup D$, Theorem 3 takes $S\subseteq E$ → `IsExchangeable` with arbitrary `S`, here `S ⊆ M.E`; reason: the page is ambiguous on how the definition applies when $S\not\subseteq B\cup D$; for $t\in B\cup D$, $X\subseteq B\cup D$ the condition is the same as for $S\cap(B\cup D)$, and $|B\cap S|$, $|D\cap S|$, $D\setminus S$ are unchanged
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Theorem 3, first sentence, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MatroidEquitability_IsExchangeable

namespace MatroidEquitability

/-- Theorem 3 (Akrami, Liu, Raj, Végh), existence clause: if `B, D` are disjoint bases and
`|B ∩ S| > |D ∩ S|`, there are `t ∈ D \ S` and a `(t, S)`-exchangeable set for `B` and `D`
(printed p.8 = PDF p.10 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…); imported there from *Matroids are equitable*, Combinatorica 46(3), 2026, Theorem 1.4).

**Formalization Note.** The theorem's second sentence, on polynomial time, is not stated here. Finite
matroid, `ncard` on subsets of bases. -/
theorem theorem_3_exists {α : Type*} (M : Matroid α) [M.Finite] (B D S : Set α)
    (hB : M.IsBase B) (hD : M.IsBase D) (hBD : Disjoint B D) (hS : S ⊆ M.E)
    (hcard : (D ∩ S).ncard < (B ∩ S).ncard) :
    ∃ t ∈ D \ S, ∃ X, IsExchangeable M B D t S X := by sorry

end MatroidEquitability
