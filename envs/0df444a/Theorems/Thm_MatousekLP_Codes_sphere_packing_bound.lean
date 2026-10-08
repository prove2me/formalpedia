-- Prove2me | Theorems.Thm_MatousekLP_Codes_sphere_packing_bound
-- name    : MatousekLP.Codes.sphere_packing_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:03:14.736443+00:00
-- url     : https://prove2.me/theorems/a52663a0-52ae-4c5c-97b1-4fff5a145ecf
-- title:
--   Lemma 8.4.2 — sphere-packing bound $A(n,2r+1) \le \lfloor 2^n/\sum_{i\le r}\binom ni\rfloor$
-- statement:
--   For all integers $n, r \ge 0$,
--   $$
--   A(n, 2r+1) \;\le\; \left\lfloor \frac{2^n}{\sum_{i=0}^{r}\binom{n}{i}} \right\rfloor ,
--   $$
--   where $A(n,d)$ is the maximum size of a code $C \subseteq \{0,1\}^n$ with distance $d$.
--
--   This is the classical volume bound on codes correcting $r$ errors; for example it gives $A(7,3) \le 16$ and $A(17,3) \le 7281$, the benchmark the Delsarte bound improves.
--
--   **Formalization Note** The floor of the quotient is natural-number division `2 ^ n / ∑ i ∈ range (r+1), n.choose i`; the denominator is at least $\binom n0 = 1$, so no division by zero occurs.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 159, Lemma 8.4.2 (Sphere-packing bound)

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic

open Finset

namespace MatousekLP.Codes

/-- Lemma 8.4.2 (Sphere-packing bound), p. 159: for all `n` and `r`,
`A(n, 2r+1) ≤ ⌊2^n / ∑_{i=0}^r (n choose i)⌋`. Natural-number division is floor division,
and the denominator is at least `(n choose 0) = 1`. -/
theorem sphere_packing_bound (n r : ℕ) :
    A n (2 * r + 1) ≤ 2 ^ n / ∑ i ∈ Finset.range (r + 1), n.choose i := by sorry

end MatousekLP.Codes
