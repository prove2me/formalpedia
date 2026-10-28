-- Prove2me | Theorems.Thm_HHRControl_PV_claim_4_41
-- name    : HHRControl.PV.claim_4_41
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:23.095865+00:00
-- url     : https://prove2.me/theorems/03739fe7-f4c2-48e8-b1fd-522bb59f7fcd
-- title:
--   Claim 4.41, p. 28 — for restricted Construction 4.28: hitting set ⇔ w can be made unique TP winner ⇔ c can be dethroned
-- statement:
--   Let $(C,V)$ be an election of Construction 4.28 for the Hitting Set instance $(B,S,k)$, with $m=\|B\|$ and $n=\|S\|$.
--
--   **Claim 4.41.** If $n(k+1)+1\le m-k$, then the following three statements are equivalent:
--   1. $S$ has a hitting set of size at most $k$.
--   2. $V$ can be partitioned such that $w$ is the unique plurality winner in the TP model.
--   3. $V$ can be partitioned such that $c$ is not the unique plurality winner in the TP model.
--
--   Here "in the TP model" refers to the two-stage election: each part nominates all its plurality winners and the nominees run against each other with voter set $V$. Together with Theorem 4.39, this claim gives Corollary 4.42.
--
--   The Lean statement gives the equivalences as $(1)\Leftrightarrow(2)$ and $(2)\Leftrightarrow(3)$.
--
--   Differences from the source:
--   - reading: Construction 4.28: the remaining candidates, and the elements of Sᵢ, follow "in some arbitrary order" → the claim is stated for every profile satisfying IsConstruction428 (any orders, any order of the voters); reason: the paper's arbitrary choice is universal; one canonical order would be a special case
--   - encoding: n(k + 1) + 1 ≤ m − k → n * (k + 1) + 1 + k ≤ m; reason: avoids natural-number subtraction; the two inequalities have the same solutions (the left side is ≥ 1)
--   - encoding: candidates B ∪ {c, w} with B = {b1, …, bm}; S = {S1, …, Sn} → candidates Fin (m + 2) with bⱼ = candB (j − 1), c = candC m = m, w = candW m = m + 1; S : Fin n → Finset (Fin m); reason: 0-based indices; no instance changes
--   - encoding: a partition of V into V1 and V2 → V₁ : Finset (Fin N) and V₂ = V₁ᶜ; reason: every partition is of this form (either part may be empty)
--   - encoding: the three statements are equivalent → (1) ↔ (2) ∧ (2) ↔ (3); reason: the same three-way equivalence
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 28, Claim 4.41

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections
import Definitions.Def_HHRControl_PV_Languages
import Definitions.Def_HHRControl_PV_Construction428

namespace HHRControl.PV

open CookPvsNP

/-- Claim 4.41, p. 28: in an election of Construction 4.28 with `n(k + 1) + 1 ≤ m − k`, the
following are equivalent: (1) `S` has a hitting set of size at most `k`; (2) `V` can be partitioned
so that `w` is the unique plurality winner in model TP; (3) `V` can be partitioned so that `c` is
not the unique plurality winner in model TP. -/
theorem claim_4_41 (m n k : ℕ) (S : Fin n → Finset (Fin m)) {N : ℕ} (P : Fin N → Ranking (m + 2))
    (hP : IsConstruction428 m n k S P) (hmk : n * (k + 1) + 1 + k ≤ m) :
    ((∃ B' : Finset (Fin m), B'.card ≤ k ∧ IsHittingSet S B') ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ∧
      ((∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ = {candW m}) ↔
        ∃ V₁ : Finset (Fin N), twoStage .TP plurality P V₁ ≠ {candC m}) := by sorry

end HHRControl.PV
