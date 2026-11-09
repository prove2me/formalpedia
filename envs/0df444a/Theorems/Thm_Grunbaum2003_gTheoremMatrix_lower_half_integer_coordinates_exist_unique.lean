-- Prove2me | Theorems.Thm_Grunbaum2003_gTheoremMatrix_lower_half_integer_coordinates_exist_unique
-- name    : Grunbaum2003.gTheoremMatrix_lower_half_integer_coordinates_exist_unique
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:06:41.162523+00:00
-- url     : https://prove2.me/theorems/ad00d0f9-647e-4845-a810-5824eca50287
-- title:
--   Existence and uniqueness of integral lower-half Björner matrix coordinates
-- statement:
--   For Björner's matrix in dimension $d$, put $m=\lfloor d/2\rfloor$. The lower-half transform
--   $$T_d(g)_k=\sum_{i=0}^{m}g_iM_{d,i,k}\qquad(0\le k\le m)$$
--   has integral coordinates for every prescribed integral input, and those coordinates are unique on $0,\ldots,m$.
--
--   Indeed, the definition gives $M_{d,i,k}=0$ when $k<i\le m$ and $M_{d,k,k}=1$. Thus
--   $$T_d(g)_k=\sum_{i<k}g_iM_{d,i,k}+g_k.$$
--   Given any $f:\mathbb N\to\mathbb Z$, define recursively
--   $$g_k=f_k-\sum_{i<k}g_iM_{d,i,k}.$$
--   This is a recursion on smaller indices and constructs integer values without division. Substitution proves $T_d(g)_k=f_k$ for $k\le m$.
--
--   If two sequences have the same transform, strong induction on $k$ gives equality of their entries: the preceding coordinates agree by induction, so the triangular formula forces equality of the $k$th entries.
--
--   Only the entries through $m$ are determined; the statement imposes no uniqueness on the unused tail. No nonnegativity or Macaulay inequalities are asserted. Applied to the augmented lower face data $f_0=1$ and $f_k=f_{k-1}(P)$ for $k>0$, this separates integer coefficient construction from the geometric and positivity content still needed in the $g$-theorem.
--
--   Source: Grünbaum, *Convex Polytopes*, second edition (2003), §10.6, p. 198a / PDF p. 235 (Björner's displayed matrix); the proof is elementary triangular elimination for that matrix.
-- source:
--   Branko Grünbaum, Convex Polytopes, second edition (Springer, 2003), §10.6, p. 198a / PDF p. 235 (Björner matrix); elementary triangular elimination for the displayed matrix.

import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem gTheoremMatrix_lower_half_integer_coordinates_exist_unique (d : ℕ) :
    (∀ f : ℕ → ℤ, ∃ g : ℕ → ℤ, ∀ k : ℕ, k ≤ d / 2 →
      ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i k = f k) ∧
    (∀ g h : ℕ → ℤ,
      (∀ k : ℕ, k ≤ d / 2 →
        ∑ i ∈ Finset.range (d / 2 + 1), g i * gTheoremMatrix d i k =
        ∑ i ∈ Finset.range (d / 2 + 1), h i * gTheoremMatrix d i k) →
      ∀ k : ℕ, k ≤ d / 2 → g k = h k) := by sorry

end Grunbaum2003
