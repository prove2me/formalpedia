-- Prove2me | Theorems.Thm_GNFS_card_sqrt_ne_pm_ge_half
-- name    : GNFS.card_sqrt_ne_pm_ge_half
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:29:47.343082+00:00
-- url     : https://prove2.me/theorems/14908692-9702-46b6-8785-f2a7a3517a8e
-- title:
--   At least half of the square roots of $x^2$ mod $n$ are $\ne \pm x$
-- statement:
--   Let $n$ be an odd natural number with at least two distinct prime factors, and let $x$ be a unit of $\mathbb{Z}/n\mathbb{Z}$. Let
--   $$R = \{\, y \in \mathbb{Z}/n\mathbb{Z} : y^2 = x^2 \,\}, \qquad R' = \{\, y \in R : y \ne x,\ y \ne -x \,\}.$$
--   Then
--   $$|R| \le 2\,|R'| .$$
--
--   So if $y$ is a uniformly random square root of $x^2$ modulo $n$, then with probability at least $1/2$ we have $y \not\equiv \pm x$, and $\gcd(x - y, n)$ is a nontrivial factor of $n$.
--
--   **Formalization Note** The hypotheses (odd, at least two distinct prime factors, $x$ a unit) are the standard setting of the source's "probability at least $1/2$" claim. The conclusion fails for prime powers, e.g. $n = 9$.
-- source:
--   Wikipedia, "General number field sieve" (revision oldid=1377718368, https://en.wikipedia.org/w/index.php?title=General_number_field_sieve&oldid=1377718368), section 'Method — Postprocessing'

import Mathlib
import Definitions.Def_GNFS_defs
open Polynomial IntermediateField

namespace GNFS
theorem card_sqrt_ne_pm_ge_half (n : ℕ) [NeZero n] (hodd : Odd n)
    (hk : 2 ≤ n.primeFactors.card) (x : ZMod n) (hx : IsUnit x) :
    (Finset.univ.filter fun y : ZMod n => y ^ 2 = x ^ 2).card ≤
      2 * (Finset.univ.filter fun y : ZMod n => y ^ 2 = x ^ 2 ∧ y ≠ x ∧ y ≠ -x).card := by sorry
end GNFS
