-- Prove2me | Theorems.Thm_KKBinPacking_GeometricGrouping_anyFit_card_le
-- name    : KKBinPacking.GeometricGrouping.anyFit_card_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T17:18:48.081409+00:00
-- url     : https://prove2.me/theorems/2ff92ced-97ae-493b-98aa-8a7700b97db2
-- title:
--   Lemma 3 — inserting small pieces costs at most $\max(A, (1+g)\,OPT(I)+1)$ bins
-- statement:
--   Let $I$ be an instance and $g$ a real number with $0 < g \le 1$. Call a piece **large** if its size is $> g/2$ and **small** otherwise. Start from any packing of the large pieces of $I$ into $A$ bins, and insert the small pieces one at a time, starting a new bin only when a piece fits in no existing bin. Then every packing $P$ that this process can produce satisfies
--
--   $$|P| \le \max\bigl(A,\ (1+g)\,OPT(I) + 1\bigr).$$
--
--   ALGORITHM 2 uses this lemma with parameter $2g$ at Step 4, where the eliminated pieces of size $\le g$ are reinserted.
--
--   **Formalization Note** The insertion process is the relation `AnyFit` (any order, any bin where the piece fits). The paper's "$g$ between 0 and 1" is read as $0 < g \le 1$.
-- source:
--   Karmarkar, Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem, Proc. 23rd FOCS, 1982, p. 314, Lemma 3

import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_AnyFit
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem anyFit_card_le (I : Multiset ℝ) (hI : IsInstance I) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (P₀ : Multiset (Multiset ℝ)) (hP₀ : IsPacking (I.filter (fun x => g / 2 < x)) P₀)
    (P : Multiset (Multiset ℝ)) (hP : AnyFit P₀ (I.filter (fun x => x ≤ g / 2)) P) :
    (Multiset.card P : ℝ) ≤ max (Multiset.card P₀ : ℝ) ((1 + g) * (OPT I : ℝ) + 1) := by sorry
end KKBinPacking.GeometricGrouping
