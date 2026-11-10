-- Prove2me | Theorems.Thm_Grunbaum2003_g_theorem_sufficiency_pos_g2_from_upper_triangular
-- name    : Grunbaum2003.g_theorem_sufficiency_pos_g2_from_upper_triangular
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T02:37:26.998652+00:00
-- url     : https://prove2.me/theorems/d5787fb7-50e6-41f8-8f93-b261f385e12e
-- title:
--   Sufficiency of the g-Theorem for M-Sequences with Positive g2 from Upper-Triangular Identities
-- statement:
--   Given the unit upper-triangular identities for gTheoremMatrix d, realizes any M-sequence g with g 1 > 0 and g 2 > 0 by a simplicial d-polytope P in R^d with faceCount P 0 = d + 1 + g 1 and faceCount P 1 = (d + 1).choose 2 + d * g 1 + g 2.
-- source:
--   Grünbaum, Convex Polytopes (2003), §10.6; Billera–Lee (1981)

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem g_theorem_sufficiency_pos_g2_from_upper_triangular (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : 0 < g 1) (hg2 : 0 < g 2)
    (hUpper :
      (∀ (i k : ℕ), k < i → i ≤ d / 2 → gTheoremMatrix d i k = 0) ∧
      (∀ (k : ℕ), k ≤ d / 2 → gTheoremMatrix d k k = 1) ∧
      (∀ (k : ℕ), k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i k =
          (∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) + (g k : ℤ)) ∧
      (∀ (k : ℕ), k ≤ d →
        gTheoremMatrix d 0 k = (Nat.choose (d + 1) k : ℤ))) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      faceCount P 0 = d + 1 + g 1 ∧
      faceCount P 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by sorry

end Grunbaum2003
