-- Prove2me | Theorems.Thm_GNFS_nontrivial_gcd_of_sq_eq_sq
-- name    : GNFS.nontrivial_gcd_of_sq_eq_sq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:29:23.012991+00:00
-- url     : https://prove2.me/theorems/3019f563-ab97-4a94-9a8e-e13e1dffdb73
-- title:
--   Congruence of squares gives a nontrivial factor
-- statement:
--   Let $n \in \mathbb{N}$ and $x, y \in \mathbb{Z}$ with
--   $$n \mid x^2 - y^2, \qquad n \nmid x - y, \qquad n \nmid x + y.$$
--   Then $\gcd(x - y, n)$ is a nontrivial divisor of $n$:
--   $$1 < \gcd(x-y, n) < n.$$
--
--   This is the final step of every congruence-of-squares factoring method.
-- source:
--   Wikipedia, "General number field sieve" (revision oldid=1377718368, https://en.wikipedia.org/w/index.php?title=General_number_field_sieve&oldid=1377718368), section 'Method — Postprocessing'

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial IntermediateField

namespace GNFS
theorem nontrivial_gcd_of_sq_eq_sq (n : ℕ) (x y : ℤ) (h : (n : ℤ) ∣ x ^ 2 - y ^ 2)
    (hsub : ¬ (n : ℤ) ∣ x - y) (hadd : ¬ (n : ℤ) ∣ x + y) :
    1 < Int.gcd (x - y) n ∧ Int.gcd (x - y) n < n := by sorry
end GNFS
