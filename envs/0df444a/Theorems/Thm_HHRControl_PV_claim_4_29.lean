-- Prove2me | Theorems.Thm_HHRControl_PV_claim_4_29
-- name    : HHRControl.PV.claim_4_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:29.850253+00:00
-- url     : https://prove2.me/theorems/944991fd-2a61-4940-aa31-d4cdaefbf220
-- title:
--   Claim 4.29, p. 24 — a hitting set B′ of size k makes w the unique plurality winner of (B′ ∪ {c, w}, V)
-- statement:
--   Let $(C,V)$ be an election of Construction 4.28 for the Hitting Set instance $(B,S,k)$: candidates $B\cup\{c,w\}$ with $B=\{b_1,\dots,b_m\}$, a positive integer $k\le m$, and the voters listed there.
--
--   **Claim 4.29.** If $B'\subseteq B$ is a hitting set of $S$ of size $k$, then $w$ is the unique plurality winner of the election
--   $$(B'\cup\{c,w\},\,V).$$
--
--   It is the first half of the correctness of the reduction from Hitting Set.
--
--   Differences from the source:
--   - reading: Construction 4.28: the remaining candidates, and the elements of Sᵢ, follow "in some arbitrary order" → the claim is stated for every profile satisfying IsConstruction428 (any orders, any order of the voters); reason: the paper's arbitrary choice is universal; one canonical order would be a special case
--   - encoding: candidates B ∪ {c, w} with B = {b1, …, bm}; S = {S1, …, Sn} → candidates Fin (m + 2) with bⱼ = candB (j − 1), c = candC m = m, w = candW m = m + 1; S : Fin n → Finset (Fin m); reason: 0-based indices; no instance changes
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 24, Claim 4.29

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.29, p. 24: in an election of Construction 4.28, if `B′` is a hitting set of `S` of size
`k`, then `w` is the unique plurality winner of the election `(B′ ∪ {c, w}, V)`. -/
theorem claim_4_29 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (B' : Finset (Fin m)) (hcard : B'.card = k)
    (hhit : IsHittingSet S B') :
    plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) Finset.univ =
      {candW m} := by sorry

end HHRControl.PV
