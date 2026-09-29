-- Prove2me | Theorems.Thm_Nullstellensatz_strong_nullstellensatz_system
-- name    : Nullstellensatz.strong_nullstellensatz_system
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:04:20.365976+00:00
-- url     : https://prove2.me/theorems/df75824d-ca40-4b7e-84d6-33ab933fd938
-- title:
--   Full Nullstellensatz for a system of polynomial equations
-- statement:
--   Let $K$ be an algebraically closed field, let $f_1,\dots,f_m \in K[X_1,\dots,X_n]$ and let $f \in K[X_1,\dots,X_n]$. Every solution $a \in K^n$ of the system $f_1 = \cdots = f_m = 0$ is also a solution of $f = 0$ if and only if there exist a natural number $r$ and polynomials $g_1,\dots,g_m$ such that
--   $$f^r = g_1 f_1 + \cdots + g_m f_m.$$
--
--   This refines the weak form, which is the case $f = 1$.
--
--   **Formalization Note.** The target polynomial is called $p$ in Lean; $r = 0$ is allowed (then $f^0 = 1$).
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, introduction (lead section), last displayed identity f^r = g_1 f_1 + ... + g_m f_m.

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem strong_nullstellensatz_system {K : Type*} [Field K] [IsAlgClosed K] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) K) (p : MvPolynomial (Fin n) K) :
    (∀ a : Fin n → K, (∀ i, eval a (f i) = 0) → eval a p = 0) ↔
      ∃ r : ℕ, ∃ g : Fin m → MvPolynomial (Fin n) K, p ^ r = ∑ i, g i * f i := by sorry

end Nullstellensatz
