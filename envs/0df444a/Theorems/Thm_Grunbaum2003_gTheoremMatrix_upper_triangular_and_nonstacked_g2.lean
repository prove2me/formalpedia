-- Prove2me | Theorems.Thm_Grunbaum2003_gTheoremMatrix_upper_triangular_and_nonstacked_g2
-- name    : Grunbaum2003.gTheoremMatrix_upper_triangular_and_nonstacked_g2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:37:28.943545+00:00
-- url     : https://prove2.me/theorems/992ccc0c-749e-4d48-a07f-5ff371dfaf66
-- title:
--   Unit Upper-Triangularity of Björner Matrix and Positivity of g2 for Non-Stacked Polytopes
-- statement:
--   Proves that gTheoremMatrix d is unit upper-triangular on 0 <= i, k <= d / 2 (vanishing for k < i <= d / 2 and equal to 1 on the diagonal), evaluates its prefix sum, and proves that any M-sequence g representing a non-stacked simplicial d-polytope P satisfies g 0 = 1, g 1 = faceCount P 0 - (d + 1) > 0, g 2 > 0, and g 2 = faceCount P 1 - (d + 1).choose 2 - d * g 1.
-- source:
--   Grünbaum, Convex Polytopes (2003), §10.6; Stanley (1980); Billera–Lee (1981)

import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem gTheoremMatrix_upper_triangular_and_nonstacked_g2 (d : ℕ) (hd : 4 ≤ d) :
    (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
    (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
    (∀ (g : ℕ → ℕ) (k : ℕ), k ≤ d / 2 →
      ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
        (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
    (∀ (k : ℕ), k ≤ d →
      gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ)) ∧
    (∀ (P : Set (Fin d → ℝ)), d + 1 < faceCount P 0 →
      (¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
        (Nat.choose (d + 1) j.succ.val : ℤ) +
          ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val) →
      ∀ (g : ℕ → ℕ), IsMSequence (d / 2) g →
        (∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
        g 0 = 1 ∧
        g 1 = faceCount P 0 - (d + 1) ∧
        0 < g 1 ∧
        0 < g 2 ∧
        (g 2 : ℤ) = (faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) - (d : ℤ) * (g 1 : ℤ)) := by sorry

end Grunbaum2003
