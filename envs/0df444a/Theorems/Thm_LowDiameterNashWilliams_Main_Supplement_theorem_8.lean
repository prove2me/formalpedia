-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_theorem_8
-- name    : LowDiameterNashWilliams.Main.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:44:26.2698+00:00
-- url     : https://prove2.me/theorems/18485177-bba9-42fd-9b2d-c2f81e21e405
-- title:
--   Theorem 8 (companion theorem; not used in the proof of the goal) — Bounded-size and frequency Set Cover gap
-- statement:
--   There exists a positive integer $B_0$ such that for every fixed integer $B>B_0$ it is NP-hard to distinguish these cases. The input is a nonempty finite universe $U'$, nonempty indexed sets covering $U'$, and an integer $0\le\beta\le m'$. Each set has size at most $B$, and each element has frequency at most $B$. With $\tau'$ the minimum cover size, distinguish
--   $$\mathrm{YES}:\quad\tau'\le\beta,\qquad
--   \mathrm{NO}:\quad\tau'>\frac{\beta}{10}\ln B.$$
--   The case $\beta=0$ remains a valid NO input. The reduction is polynomial in the full binary/incidence input length for each fixed $B$, with actual Cook machine execution. This is the bounded-frequency companion theorem used to establish Theorem 6.
--
--   Differences from the source:
--   - encoding: finite nonempty universe and indexed sets, permitting repetitions → published SCInstance with ValidCover, multiplicity frequency and a finite minimum over all index covers; reason: this has exactly the source instances; the no-cover fallback is excluded by validity
--   - encoding: NP-hardness for every fixed parameter → GapNPHard of explicit self-delimiting binary input codes using CookPvsNP polynomial-time machines; reason: this is polynomial-time many-one promise hardness; all validity constraints occur on both output sides and reductions may depend on the fixed parameter
--   - encoding: input integer 0 <= beta <= m-prime → natural beta, with its upper bound in both predicates and its binary code appended to the incidence matrix; reason: natural integers enumerate exactly this interval and retain beta=0
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 8, p. 33 (PDF p. 34)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Promises

set_option autoImplicit false
open scoped ENNReal NNReal
open scoped BigOperators
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
open SetCoverThreshold.SetCover

namespace LowDiameterNashWilliams.Main.Supplement

theorem theorem_8 :
    ∃ B₀ : ℕ, 0 < B₀ ∧ ∀ B : ℕ, B₀ < B →
      GapNPHard ThresholdInput.encode (BoundedYes B) (BoundedNo B) := by sorry

end LowDiameterNashWilliams.Main.Supplement
