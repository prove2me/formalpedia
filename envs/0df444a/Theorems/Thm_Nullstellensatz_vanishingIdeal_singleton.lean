-- Prove2me | Theorems.Thm_Nullstellensatz_vanishingIdeal_singleton
-- name    : Nullstellensatz.vanishingIdeal_singleton
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:08:28.993149+00:00
-- url     : https://prove2.me/theorems/c744a368-fe0d-4318-917a-52d885382746
-- title:
--   $\mathrm I(\{a\}) = (X_1 - a_1, \dots, X_n - a_n)$ is maximal
-- statement:
--   Let $K$ be algebraically closed and $a = (a_1,\dots,a_n) \in K^n$. Then
--   $$\mathrm I(\{a\}) = (X_1 - a_1, \dots, X_n - a_n),$$
--   and this ideal is a maximal ideal of $K[X_1,\dots,X_n]$.
--
--   **Formalization Note.** The statement is kept in the article's setting ($K$ algebraically closed), although neither part needs that hypothesis.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 6, first two sentences (I({a}) is a maximal ideal).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem vanishingIdeal_singleton {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (a : Fin n → K) :
    vanishingIdeal {a} = pointIdeal a ∧ (pointIdeal a).IsMaximal := by sorry

end Nullstellensatz
