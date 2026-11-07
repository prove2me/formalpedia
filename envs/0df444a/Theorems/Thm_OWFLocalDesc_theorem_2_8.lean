-- Prove2me | Theorems.Thm_OWFLocalDesc_theorem_2_8
-- name    : OWFLocalDesc.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:44.400079+00:00
-- url     : https://prove2.me/theorems/a7b7410e-a7c9-4c85-80e3-1238ea4ac241
-- title:
--   Theorem 2.8 (Amplification): weak one-way functions exist iff one-way functions exist
-- statement:
--   Weak one-way functions exist if and only if one-way functions exist, both in the sense of Definition 2.7 against PPT inverters given $1^n$.
--
--   The easiness direction (Theorem 5.1) uses the contrapositive: without one-way functions, every polynomial-time function has, for every positive polynomial $R$, a PPT inverter succeeding with probability at least $1-1/R(N)$ for infinitely many $N$.
--
--   Differences from the source:
--   - encoding: PPT inverters given (1^n, f(u)) → `PPT`: one `CookPvsNP.PolyTimeComputable` machine on the code of (coins, input), coin count polynomial in the input length; input `tupleCode [1^n, f(u)]`; reason: the standard uniform PPT model with fixed injective codes; no instance changes
--   - encoding: positive polynomials R (weak one-way) and p (negligible, Definition 2.2) → polynomials in ℕ[X] with values ≥ 1 everywhere; reason: every positive real polynomial is dominated pointwise by such a polynomial, and both bounds are monotone in the polynomial, so the notions are unchanged
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 2.8, p.14 (cited from [Yao82, Gol01, Gol95])

import Mathlib
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_WeakOWFExist
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Theorem 2.8 (Amplification), cited from [Yao82, Gol01, Gol95].** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Theorem 2.8, p.14: "Weak one-way functions exist if and only if one-way functions exist."

**Formalization Note.** Both notions are Definition 2.7's, against uniform PPT inverters given
`1ⁿ`, with the weak notion's failure bound `1/R(n)` holding eventually for each inverter. -/
theorem theorem_2_8 : WeakOWFExist ↔ OWFExist := by sorry

end OWFLocalDesc
