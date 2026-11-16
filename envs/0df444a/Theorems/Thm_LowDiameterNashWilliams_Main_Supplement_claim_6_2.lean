-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_6_2
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:40:30.124229+00:00
-- url     : https://prove2.me/theorems/b84f0fe8-69f2-4088-b02d-7e3f8cdbcac9
-- title:
--   Claim 6.2 (used in the proof of Theorem 6) — LP source-size bounds
-- statement:
--   Let $D\ge1$, $B=\lfloor\sqrt{D/2}\rfloor$, and let the source Set Cover instance have nonempty universe $U'$, nonempty indexed sets covering it, set sizes and frequencies at most $B$, and integer $0\le\beta\le m'$. If $x$ satisfies LP (4), then
--   $$|U'|\le B\beta,\qquad m'\le B^2\beta.$$
--   Both source-size bounds are retained. They control the output size and the gap in the feasible branch of the reduction.
--
--   Differences from the source:
--   - encoding: finite nonempty universe and indexed sets, permitting repetitions → published SCInstance with ValidCover, multiplicity frequency and a finite minimum over all index covers; reason: this has exactly the source instances; the no-cover fallback is excluded by validity
--   - encoding: B=floor(sqrt(D/2)) → Nat.sqrt (D / 2); reason: for integer D the natural square-root formula equals the source floor of the real square root
--   - generalization: D is sufficiently large in the surrounding reduction → every positive D with the same bounded-instance and feasible-LP hypotheses; reason: the displayed inequalities use only these local constraints; this includes all source D
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 6.2, p. 34 (PDF p. 35)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_SetCover

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_6_2 (D β : ℕ) (hD : 0 < D) (I : SCInstance)
    (hI : BoundedCover I (Nat.sqrt (D / 2))) (hβ : β ≤ I.sets.length)
    (x : Fin I.sets.length → ℝ) (hx : FeasibleLP I β x) :
    I.n ≤ Nat.sqrt (D / 2) * β ∧ I.sets.length ≤ (Nat.sqrt (D / 2))^2 * β := by sorry

end LowDiameterNashWilliams.Main.Supplement
