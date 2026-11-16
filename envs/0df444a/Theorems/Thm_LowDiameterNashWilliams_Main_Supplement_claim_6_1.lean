-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_6_1
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:39:46.42517+00:00
-- url     : https://prove2.me/theorems/45b91af9-de74-4baf-8906-82012a2c001e
-- title:
--   Claim 6.1 (used in the proof of Theorem 6) — Replication count bounds
-- statement:
--   Let $D\ge1$, $B=\lfloor\sqrt{D/2}\rfloor$, and let the source Set Cover instance have nonempty universe $U'$, nonempty indexed sets covering it, set sizes and frequencies at most $B$, and an integer $0\le\beta\le m'$. Suppose $x$ satisfies all constraints of LP (4). Set $r_j=\lceil Dx_j\rceil+1$ and $m=D\beta+2m'$. Then both bounds hold:
--   $$\sum_{j=1}^{m'}r_j\le m,\qquad \sum_{j:u\in S'_j}r_j\ge D\quad(u\in U').$$
--   These are conclusions about any feasible point, not data stored in the LP model; they justify the replication step.
--
--   Differences from the source:
--   - encoding: finite nonempty universe and indexed sets, permitting repetitions → published SCInstance with ValidCover, multiplicity frequency and a finite minimum over all index covers; reason: this has exactly the source instances; the no-cover fallback is excluded by validity
--   - encoding: B=floor(sqrt(D/2)) and integer ceil(D*x_j) → Nat.sqrt (D / 2) and natural ceiling on a feasible nonnegative x_j; reason: the natural formulas equal the source formulas on this domain
--   - generalization: D is sufficiently large in the surrounding reduction → every positive D with the same bounded-instance and feasible-LP hypotheses; reason: the displayed inequalities use only these local constraints; this includes all source D
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 6.1, p. 33 (PDF p. 34)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_SetCover

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_6_1 (D β : ℕ) (hD : 0 < D) (I : SCInstance)
    (hI : BoundedCover I (Nat.sqrt (D / 2))) (hβ : β ≤ I.sets.length)
    (x : Fin I.sets.length → ℝ) (hx : FeasibleLP I β x) :
    (∑ j : Fin I.sets.length, replicationCount D (x j)) ≤ replicationSize I D β ∧
    ∀ u : Fin I.n,
      D ≤ ∑ j : Fin I.sets.length, if u ∈ I.sets.get j then replicationCount D (x j) else 0 := by sorry

end LowDiameterNashWilliams.Main.Supplement
