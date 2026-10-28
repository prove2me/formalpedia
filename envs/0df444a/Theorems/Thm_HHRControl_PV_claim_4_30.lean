-- Prove2me | Theorems.Thm_HHRControl_PV_claim_4_30
-- name    : HHRControl.PV.claim_4_30
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:44.684836+00:00
-- url     : https://prove2.me/theorems/9b6f0b0b-746a-414e-9732-3aeb2b64a049
-- title:
--   Claim 4.30, p. 24 — if c is not the unique plurality winner of (D ∪ {c}, V), then D = B′ ∪ {w} for a hitting set B′ of size ≤ k
-- statement:
--   Let $(C,V)$ be an election of Construction 4.28 for the Hitting Set instance $(B,S,k)$: candidates $B\cup\{c,w\}$ with $B=\{b_1,\dots,b_m\}$, a positive integer $k\le m$, and the voters listed there.
--
--   **Claim 4.30.** Let $D\subseteq B\cup\{w\}$. If $c$ is not the unique plurality winner of the election $(D\cup\{c\},V)$, then there exists a set $B'\subseteq B$ such that
--   1. $D=B'\cup\{w\}$,
--   2. $w$ is the unique plurality winner of the election $(B'\cup\{c,w\},V)$, and
--   3. $B'$ is a hitting set of $S$ of size at most $k$.
--
--   It is the second half of the correctness of the reduction from Hitting Set, and is used for Claim 4.41.
--
--   Differences from the source:
--   - reading: Construction 4.28: the remaining candidates, and the elements of Sᵢ, follow "in some arbitrary order" → the claim is stated for every profile satisfying IsConstruction428 (any orders, any order of the voters); reason: the paper's arbitrary choice is universal; one canonical order would be a special case
--   - encoding: candidates B ∪ {c, w} with B = {b1, …, bm}; S = {S1, …, Sn} → candidates Fin (m + 2) with bⱼ = candB (j − 1), c = candC m = m, w = candW m = m + 1; S : Fin n → Finset (Fin m); reason: 0-based indices; no instance changes
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 24, Claim 4.30

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.30, p. 24: in an election of Construction 4.28, let `D ⊆ B ∪ {w}`. If `c` is not the
unique plurality winner of `(D ∪ {c}, V)`, then `D = B′ ∪ {w}` for a set `B′ ⊆ B` such that `w` is
the unique plurality winner of `(B′ ∪ {c, w}, V)` and `B′` is a hitting set of `S` of size at most
`k`. -/
theorem claim_4_30 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (D : Finset (Fin (m + 2)))
    (hD : D ⊆ Finset.univ.image candB ∪ {candW m})
    (hc : plurality.winners (m + 2) N P (insert (candC m) D) Finset.univ ≠ {candC m}) :
    ∃ B' : Finset (Fin m), D = B'.image candB ∪ {candW m} ∧
      plurality.winners (m + 2) N P (B'.image candB ∪ {candC m, candW m}) Finset.univ =
        {candW m} ∧
      B'.card ≤ k ∧ IsHittingSet S B' := by sorry

end HHRControl.PV
