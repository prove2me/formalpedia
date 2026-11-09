-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_necessity_nonstacked_pos_g2
-- name    : Grunbaum2003.g_theorem_necessity_nonstacked_pos_g2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-09T02:37:28.884536+00:00
-- url     : https://prove2.me/theorems/f9336347-3ff9-44f2-ad07-fbc42921604c
-- title:
--   Necessity of the g-Theorem for Non-Stacked Simplicial d-Polytopes with Positive g2
-- statement:
--   Given the unit upper-triangular identities for gTheoremMatrix d, proves that every non-stacked simplicial d-polytope P (d >= 4) with faceCount P 0 > d + 1 admits an M-sequence g with g 1 = faceCount P 0 - (d + 1) > 0 and g 2 = faceCount P 1 - (d + 1).choose 2 - d * g 1 > 0 representing its face vector.
-- source:
--   Grünbaum, Convex Polytopes (2003), §10.6; Stanley (1980)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_necessity_nonstacked_pos_g2 (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) (hV_gt : d + 1 < faceCount P 0)
    (hNonStacked : ¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
      (Nat.choose (d + 1) j.succ.val : ℤ) +
        ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val)
    (hUpper :
      (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
      (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
      (∀ (g : ℕ → ℕ) (k : ℕ), k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
          (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
      (∀ (k : ℕ), k ≤ d →
        gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ))) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      g 0 = 1 ∧
      g 1 = faceCount P 0 - (d + 1) ∧
      0 < g 1 ∧
      0 < g 2 ∧
      (g 2 : ℤ) = (faceCount P 1 : ℤ) - (Nat.choose (d + 1) 2 : ℤ) - (d : ℤ) * (g 1 : ℤ) ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
