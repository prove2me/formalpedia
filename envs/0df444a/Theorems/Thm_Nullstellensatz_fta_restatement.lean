-- Prove2me | Theorems.Thm_Nullstellensatz_fta_restatement
-- name    : Nullstellensatz.fta_restatement
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:31:29.838015+00:00
-- url     : https://prove2.me/theorems/37089742-49a1-4ac3-b5d5-95c6d7f73862
-- title:
--   Fundamental theorem of algebra as the case n = 1
-- statement:
--   A polynomial $P \in \mathbb C[x]$ has a root in $\mathbb C$ if and only if
--   $$\deg P \ne 0.$$
--
--   This is the special case $K = \mathbb C$, $n = 1$ of the weak Nullstellensatz, applied to a single polynomial.
--
--   **Formalization Note.** Mathlib's degree of the zero polynomial is $-\infty \ne 0$, consistent with the fact that $0$ has roots; the nonzero constants are exactly the polynomials of degree $0$.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 4 (restatement of the fundamental theorem of algebra).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem fta_restatement (P : Polynomial ℂ) :
    (∃ z : ℂ, P.IsRoot z) ↔ P.degree ≠ 0 := by sorry

end Nullstellensatz
