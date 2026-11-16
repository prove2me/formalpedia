-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_claim_6_3
-- name    : LowDiameterNashWilliams.Main.Supplement.claim_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:40:53.161054+00:00
-- url     : https://prove2.me/theorems/ea4894e3-7710-4df9-a7b3-53dceaa2ddb4
-- title:
--   Claim 6.3 (used in the proof of Theorem 6) — Fixed NO cover instance
-- statement:
--   For all sufficiently large integers $D$, let $q$ be the largest even integer at most $\log_2D$, put $r=\lceil2D/q\rceil$, and form $U=\{X\subseteq[q]:|X|=q/2\}$. For every $j\in[q]$ take $r$ indexed copies of $A_j=\{X\in U:j\in X\}$, giving $m=qr$ sets. Then every output set is nonempty,
--   $$|U|\le m,\qquad f(u)\ge D\quad(u\in U),\qquad \tau>\frac{m}{100D}\ln D.$$
--   All four conclusions concern this particular constructed instance. A positive threshold is quantified before $D$. This supplies the fixed NO output in the infeasible LP branch.
--
--   Differences from the source:
--   - encoding: the indexed half-subset construction and its minimum cover size → the explicit fixedNoCover instance, multiplicity frequency and finite attained cover minimum; reason: for sufficiently large D, q is positive and even and every half-subset belongs to an incidence set; the construction is coverable, so the no-cover fallback is unused without assuming ValidCover
--   - encoding: q largest even integer at most log_2 D, and r=ceil(2D/q) → q=2*(Nat.log 2 D / 2), r=(2D+q-1)/q, with the half-subsets enumerated finitely; reason: for sufficiently large D these are the same integers; the existential threshold precedes D and excludes q=0
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Claim 6.3, p. 35 (PDF p. 36)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_SetCover

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn

namespace LowDiameterNashWilliams.Main.Supplement

theorem claim_6_3 :
    ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ D : ℕ, D₀ < D →
      let I := fixedNoCover D
      (∀ S ∈ I.sets, S.Nonempty) ∧ I.n ≤ I.sets.length ∧
      (∀ u, D ≤ frequency I u) ∧
      (I.sets.length : ℝ) / (100 * D) * Real.log D < coverNumber I := by sorry

end LowDiameterNashWilliams.Main.Supplement
