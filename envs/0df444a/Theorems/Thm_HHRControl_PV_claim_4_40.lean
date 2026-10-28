-- Prove2me | Theorems.Thm_HHRControl_PV_claim_4_40
-- name    : HHRControl.PV.claim_4_40
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:00.089616+00:00
-- url     : https://prove2.me/theorems/b4e70974-9111-4755-ba97-8e884fe5cd45
-- title:
--   Claim 4.40, p. 27 — in the restricted Construction 4.28, c is a plurality winner of (C, V₁) or of (C, V₂)
-- statement:
--   Let $(C,V)$ be an election of Construction 4.28 for the Hitting Set instance $(B,S,k)$, with $m=\|B\|$ and $n=\|S\|$.
--
--   **Claim 4.40.** If $n(k+1)+1\le m-k$, then for every partition of $V$ into $V_1$ and $V_2$, $c$ is a plurality winner of $(C,V_1)$ or of $(C,V_2)$.
--
--   ("A plurality winner": $c$ belongs to the winner set, possibly together with others.) It is the step of Claim 4.41 that makes $c$ always reach the final election in model TP.
--
--   Differences from the source:
--   - reading: Construction 4.28: the remaining candidates, and the elements of Sᵢ, follow "in some arbitrary order" → the claim is stated for every profile satisfying IsConstruction428 (any orders, any order of the voters); reason: the paper's arbitrary choice is universal; one canonical order would be a special case
--   - encoding: n(k + 1) + 1 ≤ m − k → n * (k + 1) + 1 + k ≤ m; reason: avoids natural-number subtraction; the two inequalities have the same solutions (the left side is ≥ 1)
--   - encoding: candidates B ∪ {c, w} with B = {b1, …, bm}; S = {S1, …, Sn} → candidates Fin (m + 2) with bⱼ = candB (j − 1), c = candC m = m, w = candW m = m + 1; S : Fin n → Finset (Fin m); reason: 0-based indices; no instance changes
--   - encoding: a partition of V into V1 and V2 → V₁ : Finset (Fin N) and V₂ = V₁ᶜ; reason: every partition is of this form (either part may be empty)
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 27, Claim 4.40

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.40, p. 27: in an election of Construction 4.28 with `n(k + 1) + 1 ≤ m − k`, for every
partition of `V` into `V₁` and `V₂`, `c` is a plurality winner of `(C, V₁)` or of `(C, V₂)`. -/
theorem claim_4_40 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m) (V₁ : Finset (Fin N)) :
    candC m ∈ plurality.winners (m + 2) N P Finset.univ V₁ ∨
      candC m ∈ plurality.winners (m + 2) N P Finset.univ V₁ᶜ := by sorry

end HHRControl.PV
