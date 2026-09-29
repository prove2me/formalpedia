-- Prove2me | Theorems.Thm_Nullstellensatz_nullstellensatz
-- name    : Nullstellensatz.nullstellensatz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T01:56:05.052934+00:00
-- url     : https://prove2.me/theorems/7ef2962b-2171-4726-8aef-bda1873e537b
-- title:
--   Hilbert's Nullstellensatz
-- statement:
--   Let $k$ be a field and $K$ an algebraically closed field extension of $k$. Let $J$ be an ideal of $k[X_1,\dots,X_n]$, and let $\mathrm V(J) \subseteq K^n$ be the set of $a \in K^n$ with $f(a) = 0$ for all $f \in J$. If $p \in k[X_1,\dots,X_n]$ vanishes on $\mathrm V(J)$, i.e. $p(a) = 0$ for all $a \in \mathrm V(J)$, then there is a natural number $r$ such that
--   $$p^r \in J.$$
--
--   This is Hilbert's Nullstellensatz (1893), the basic link between ideals of polynomial rings and the geometry of their zero sets.
--
--   **Formalization Note.** $K$ is a $k$-algebra, and polynomials over $k$ are evaluated at points of $K^n$ through the embedding $k \to K$. The algebraic set is written out inline, since it lives in $K^n$ while $J$ lives in $k[X]$.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 1 (the statement with k a field and K an algebraically closed extension; reference [2] of the article).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem nullstellensatz {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (p : MvPolynomial (Fin n) k)
    (hp : ∀ a : Fin n → K, (∀ f ∈ J, aeval a f = 0) → aeval a p = 0) :
    ∃ r : ℕ, p ^ r ∈ J := by sorry

end Nullstellensatz
