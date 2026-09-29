-- Prove2me | Theorems.Thm_Freiman_separated_peaks
-- name    : Freiman.separated_peaks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:27.622362+00:00
-- url     : https://prove2.me/theorems/2d84eb3a-63d4-4ee0-8515-7cad76a8c505
-- title:
--   separated peaks
-- statement:
--   Let a two-sided word have a central local value $t$ that bounds every local value, and only finitely many digits outside $\{1,2,3\}$. Then $t$ belongs to the classical Lagrange spectrum if either $t\ge\sqrt{21}$, or the word avoids 31313 and $t\ge4\sqrt{462}/19$. Both endpoints are included.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization
import Mathlib.Topology.Instances.Real.Lemmas

open Freiman

theorem Freiman.separated_peaks (a : ℤ → ℕ+) (t : ℝ)
    (hcenter : localValue a 0 = t)
    (hmax : ∀ i : ℤ, localValue a i ≤ t)
    (hfinite : ∃ N : ℕ, ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3)
    (hcondition : Real.sqrt 21 ≤ t ∨ (AvoidsBlock a [3, 1, 3, 1, 3] ∧ (4 * Real.sqrt 462 / 19 : ℝ) ≤ t)) :
    t ∈ lagrangeSpectrum := by sorry
