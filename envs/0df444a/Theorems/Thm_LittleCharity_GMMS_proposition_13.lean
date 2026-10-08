-- Prove2me | Theorems.Thm_LittleCharity_GMMS_proposition_13
-- name    : LittleCharity.GMMS.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:37.536285+00:00
-- url     : https://prove2.me/theorems/ddda2e90-de3d-46a9-8878-fe3f6d2ce508
-- title:
--   Proposition 13 ([20]) — deleting no more goods than agents preserves maximin share
-- statement:
--   Let $N$ be a finite set of agents with nonnegative additive valuations on a finite set $M$ of goods. Choose $N'\subseteq N$ and $M'\subseteq M$ such that $|M\setminus M'|\le |N\setminus N'|$. For every remaining agent $i\in N'$,
--
--   $$
--   \operatorname{MMS}_i(|N|,M)\le\operatorname{MMS}_i(|N'|,M').
--   $$
--
--   Thus deleting no more goods than agents cannot reduce the remaining agent's maximin-share benchmark. The paper cites this proposition from [20] and uses it to pass from a larger group and good set to smaller ones in Theorem 16.
--
--   **Formalization Note** The sets $N,N',M,M'$ may be subsets of the ambient finite agent and good types. Since $i\in N'\subseteq N$, both part counts are positive.
-- source:
--   Chaudhury, Kavitha, Mehlhorn & Sgouritsa, A Little Charity Guarantees Almost Envy-Freeness, arXiv:1907.04596v3, p. 14, Proposition 13 ([20])

import Mathlib
import Definitions.Def_LittleCharity_GMMS_Setting

namespace LittleCharity.GMMS

/-- Proposition 13 ([20]), p. 14: deleting no more goods than agents cannot lower a remaining agent's maximin share. -/
theorem proposition_13 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : LittleCharity.MMS.IsAdditive v)
    (N N' : Finset (Fin n)) (M M' : Finset (Fin m)) (hN : N' ⊆ N) (hM : M' ⊆ M)
    (hcard : (M \ M').card ≤ (N \ N').card) (i : Fin n) (hi : i ∈ N') :
    LittleCharity.MMS.mms (v i) N.card M ≤ LittleCharity.MMS.mms (v i) N'.card M' := by sorry

end LittleCharity.GMMS
