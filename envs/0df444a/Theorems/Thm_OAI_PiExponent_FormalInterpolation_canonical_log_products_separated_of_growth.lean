-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_canonical_log_products_separated_of_growth
-- name    : OAI.PiExponent.FormalInterpolation.canonical_log_products_separated_of_growth
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T12:44:02.625009+00:00
-- url     : https://prove2.me/theorems/77aaa87c-4df8-4f5f-87db-c2caa1dacba0
-- title:
--   Finite product separation from canonical weight growth
-- statement:
--   For positive exceptional weights and positive theta, a canonical sequence starting at one, bounded below by one through index m, and satisfying the stated strict growth inequality yields strict product separation for equal-cardinality index sets whose memberships agree above their first specified differing index.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.canonical_log_products_separated_of_growth
    (m : Nat) (x : Nat → Real) (w0 v0 theta C : Real)
    (hx0 : x 0 = 1)
    (hxle : ∀ n, n ≤ m → 1 ≤ x n)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hgrowth : ∀ n, 1 ≤ n → n ≤ m →
      (C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)) *
        (∏ j ∈ Finset.range n, x j) < x n) :
    let w : Fin (m + 1) → Real := fun i => Fin.cases w0 (fun j => x (j.val + 1)) i
    let v : Fin (m + 1) → Real := fun i => Fin.cases v0 (fun j => x (j.val + 1) / theta) i
    ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
          C * (∏ j ∈ B, v j) < ∏ j ∈ A, w j := by sorry
