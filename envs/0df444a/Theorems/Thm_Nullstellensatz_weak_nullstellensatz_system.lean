-- Prove2me | Theorems.Thm_Nullstellensatz_weak_nullstellensatz_system
-- name    : Nullstellensatz.weak_nullstellensatz_system
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T23:46:09.063645+00:00
-- url     : https://prove2.me/theorems/d24db747-a4a8-4f92-8cf1-382ae0ef07f7
-- title:
--   Weak Nullstellensatz for a system of polynomial equations
-- statement:
--   Let $K$ be an algebraically closed field and let $f_1, \dots, f_m \in K[X_1, \dots, X_n]$. The system
--   $$f_1(x_1,\dots,x_n) = 0, \quad \dots, \quad f_m(x_1,\dots,x_n) = 0$$
--   has no solution $(a_1,\dots,a_n) \in K^n$ if and only if there exist polynomials $g_1,\dots,g_m \in K[X_1,\dots,X_n]$ with
--   $$g_1 f_1 + \cdots + g_m f_m = 1.$$
--
--   The "if" direction is immediate (evaluate at a solution); the content is that an inconsistent system always has such an algebraic certificate.
--
--   **Formalization Note.** The polynomials are indexed by $\mathrm{Fin}\, m$; for $m = 0$ both sides are false.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, introduction (lead section), first displayed system and the identity g_1 f_1 + ... + g_m f_m = 1.

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem weak_nullstellensatz_system {K : Type*} [Field K] [IsAlgClosed K] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) K) :
    (¬ ∃ a : Fin n → K, ∀ i, eval a (f i) = 0) ↔
      ∃ g : Fin m → MvPolynomial (Fin n) K, ∑ i, g i * f i = 1 := by sorry

end Nullstellensatz
