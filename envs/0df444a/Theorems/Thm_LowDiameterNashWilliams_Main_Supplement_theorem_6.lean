-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_Supplement_theorem_6
-- name    : LowDiameterNashWilliams.Main.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:41:43.56314+00:00
-- url     : https://prove2.me/theorems/2259e79e-dfca-41a0-9ffc-c4962fcfd3f5
-- title:
--   Theorem 6 (companion theorem; not used in the proof of the goal) — Minimum-frequency Set Cover gap
-- statement:
--   There exists a positive integer $D_0$ such that for every fixed integer $D>D_0$ the following promise problem is NP-hard. The input is a nonempty finite universe $U$ and nonempty indexed sets $S_1,\ldots,S_m$ covering $U$, with $|U|\le m$ and every element of frequency at least $D$. With $\tau$ the attained minimum cover size, distinguish
--   $$\mathrm{YES}:\quad\tau\le\frac mD,\qquad
--   \mathrm{NO}:\quad\tau>\frac{m}{100D}\ln D.$$
--   Repeated sets count separately in frequency and input size. Every NP language has a polynomial-time many-one reduction preserving both promised cases. The reduction may depend on fixed $D$.
--
--   Differences from the source:
--   - encoding: finite nonempty universe and indexed sets, permitting repetitions → published SCInstance with ValidCover, multiplicity frequency and a finite minimum over all index covers; reason: this has exactly the source instances; the no-cover fallback is excluded by validity
--   - encoding: NP-hardness for every fixed parameter → GapNPHard of explicit self-delimiting binary input codes using CookPvsNP polynomial-time machines; reason: this is polynomial-time many-one promise hardness; all validity constraints occur on both output sides and reductions may depend on the fixed parameter
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Theorem 6, p. 28 (PDF p. 29)

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

theorem theorem_6 :
    ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ D : ℕ, D₀ < D →
      GapNPHard coverEncode (FrequentYes D) (FrequentNo D) := by sorry

end LowDiameterNashWilliams.Main.Supplement
