-- Prove2me | Theorems.Thm_GNFS_baseMPolynomial_spec
-- name    : GNFS.baseMPolynomial_spec
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:24:38.145344+00:00
-- url     : https://prove2.me/theorems/137d80b3-bf96-4296-95dc-0af9fdfb580e
-- title:
--   Base-$m$ polynomial: $f(m)=n$ with digits $0\le a_i<m$
-- statement:
--   Let $n, m$ be natural numbers with $m \ge 2$, and let $f_{n,m}(x) = \sum_i a_i x^i$ be the base-$m$ polynomial of $n$, whose coefficients are the base-$m$ digits of $n$. Then:
--
--   1. $f_{n,m}(m) = n$;
--   2. every coefficient satisfies $0 \le a_i < m$ (coefficients beyond the degree are $0$);
--   3. $m$ is a root of $f_{n,m}$ modulo $n$, i.e. $f_{n,m}(m) \equiv 0 \pmod n$.
--
--   This is the basic polynomial-selection step of GNFS, paired with $g(x) = x - m$.
-- source:
--   Wikipedia, "General number field sieve" (revision oldid=1377718368, https://en.wikipedia.org/w/index.php?title=General_number_field_sieve&oldid=1377718368), section 'Method — Polynomial choice'

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial IntermediateField

namespace GNFS
theorem baseMPolynomial_spec (n m : ℕ) (hm : 2 ≤ m) :
    (baseMPolynomial n m).eval (m : ℤ) = n ∧
      (∀ i, 0 ≤ (baseMPolynomial n m).coeff i ∧ (baseMPolynomial n m).coeff i < m) ∧
      ((baseMPolynomial n m).map (Int.castRingHom (ZMod n))).IsRoot (m : ZMod n) := by sorry
end GNFS
