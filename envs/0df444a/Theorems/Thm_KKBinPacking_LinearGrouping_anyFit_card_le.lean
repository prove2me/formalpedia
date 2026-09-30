-- Prove2me | Theorems.Thm_KKBinPacking_LinearGrouping_anyFit_card_le
-- name    : KKBinPacking.LinearGrouping.anyFit_card_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T11:20:47.341208+00:00
-- url     : https://prove2.me/theorems/02f7709e-d883-4114-a53d-cd00b1145778
-- title:
--   Lemma 3 — inserting small pieces costs at most $\max(A, (1+g)\,OPT(I) + 1)$ bins
-- statement:
--   Let $I$ be an instance and $0 < g \le 1$. Call a piece **large** if its size exceeds $g/2$ and **small** otherwise. Let $P_0$ be any packing of the large pieces, with $A$ bins, and let $P$ be the result of inserting the small pieces into $P_0$ one at a time, starting a new bin only when necessary. Then
--
--   $$
--   |P| \le \max\bigl(A,\ (1+g)\,OPT(I) + 1\bigr).
--   $$
--
--   The lemma justifies setting small pieces aside, packing the rest carefully, and adding the small pieces greedily at the end.
--
--   **Formalization Note** The paper takes $g$ "between 0 and 1"; the statement allows $g = 1$, which ALGORITHM 1 reaches when $n(I) = 2$. Insertion is any execution of the any-fit process (any order of pieces, any fitting bin).
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 314, Lemma 3

import Mathlib
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_AnyFit
open KKBinPacking.Shared

namespace KKBinPacking.LinearGrouping
theorem anyFit_card_le (I : Multiset ℝ) (hI : IsInstance I) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (P₀ : Multiset (Multiset ℝ)) (hP₀ : IsPacking (I.filter (fun x => g / 2 < x)) P₀)
    (P : Multiset (Multiset ℝ)) (hP : AnyFit P₀ (I.filter (fun x => x ≤ g / 2)) P) :
    (Multiset.card P : ℝ) ≤ max (Multiset.card P₀ : ℝ) ((1 + g) * (OPT I : ℝ) + 1) := by sorry
end KKBinPacking.LinearGrouping
