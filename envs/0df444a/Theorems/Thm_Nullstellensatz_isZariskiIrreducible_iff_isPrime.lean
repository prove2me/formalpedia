-- Prove2me | Theorems.Thm_Nullstellensatz_isZariskiIrreducible_iff_isPrime
-- name    : Nullstellensatz.isZariskiIrreducible_iff_isPrime
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:34:02.878992+00:00
-- url     : https://prove2.me/theorems/b789954c-f194-4b46-b2f0-18062ffd0d80
-- title:
--   Irreducible algebraic sets have prime vanishing ideals
-- statement:
--   Let $K$ be algebraically closed and $W \subseteq K^n$ an algebraic set. Then $W$ is irreducible in the Zariski topology if and only if
--   $$\mathrm I(W) \text{ is a prime ideal}.$$
--
--   **Formalization Note.** Irreducibility is expressed through closed sets: $W \ne \emptyset$, and whenever $W \subseteq W_1 \cup W_2$ with $W_1, W_2$ algebraic, $W \subseteq W_1$ or $W \subseteq W_2$.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 6, last sentence (W irreducible iff I(W) prime).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem isZariskiIrreducible_iff_isPrime {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (W : Set (Fin n → K)) (hW : IsAlgebraicSet W) :
    IsZariskiIrreducible W ↔ (vanishingIdeal W).IsPrime := by sorry

end Nullstellensatz
