-- Prove2me | Theorems.Thm_Grunbaum2003_gTheoremMatrix_lower_half_recurrence_and_dehn_sommerville_split
-- name    : Grunbaum2003.gTheoremMatrix_lower_half_recurrence_and_dehn_sommerville_split
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:01:55.268647+00:00
-- url     : https://prove2.me/theorems/1375de00-30dd-4b91-a217-dbea7d7f8517
-- title:
--   Björner matrix: lower-half recurrence assembly and first and last face-count identities
-- statement:
--   For $d\ge4$, the unit triangular shape of Björner's matrix gives
--   $$\sum_{i=0}^{\lfloor d/2\rfloor}g_i M_{d,i,k}=\sum_{i<k}g_iM_{d,i,k}+g_k\qquad(1\le k\le\lfloor d/2\rfloor).$$
--   Consequently, a sequence satisfying the lower-half recurrence and the upper-half face-count equations represents the entire face vector. This is an algebraic assembly lemma; it does not establish the Dehn–Sommerville relations or the existence of the sequence.
--
--   For an $M$-sequence representing a face vector, its initial value is $g_0=1$. Evaluation in columns $1$ and $2$ gives
--   $$f_0=d+1+g_1,\qquad f_1=\binom{d+1}{2}+dg_1+g_2.$$
--   The binomial identity
--   $$2\binom n2=n(n-1)$$
--   gives the rowwise relation
--   $$2M_{d,i,d-1}=dM_{d,i,d}\qquad(i\le\lfloor d/2\rfloor).$$
--   Summing it against the coefficients yields
--   $$2f_{d-2}=df_{d-1}.$$
--   All matrix identities are proved directly from the canonical definition; the solution imports only definitions and Mathlib.
-- source:
--   Grünbaum, Convex Polytopes, 2nd ed. (2003), §10.6, additional notes pp. 198a–198b (PDF pp. 235–236), Björner matrix formulation. This auxiliary result is an algebraic consequence of the stated matrix formula, not a proof of the Dehn–Sommerville relations.

import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem gTheoremMatrix_lower_half_recurrence_and_dehn_sommerville_split (d : ℕ) (hd : 4 ≤ d) :
    (∀ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      (∀ (k : ℕ), 1 ≤ k → k ≤ d / 2 →
        (g k : ℤ) = (faceCount P (k - 1) : ℤ) -
          ∑ i ∈ Finset.range k, (g i : ℤ) * gTheoremMatrix d i k) →
      (∀ (j : Fin d), d / 2 < j.succ.val →
        (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
      ∀ (j : Fin d),
        (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) ∧
    (∀ (P : Set (Fin d → ℝ)) (g : ℕ → ℕ),
      IsMSequence (d / 2) g →
      (∀ (j : Fin d),
        (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) →
      faceCount P 0 = d + 1 + g 1 ∧
      faceCount P 1 = Nat.choose (d + 1) 2 + d * g 1 + g 2 ∧
      2 * faceCount P (d - 2) = d * faceCount P (d - 1)) := by sorry

end Grunbaum2003
