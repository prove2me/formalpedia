-- Prove2me | Theorems.Thm_Nullstellensatz_weak_nullstellensatz
-- name    : Nullstellensatz.weak_nullstellensatz
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:08:02.645019+00:00
-- url     : https://prove2.me/theorems/3afeaaa5-97bc-434e-90a0-2147d3485431
-- title:
--   Weak Nullstellensatz
-- statement:
--   Let $k$ be a field, $K \supseteq k$ an algebraically closed field extension, and $J$ a proper ideal of $k[X_1,\dots,X_n]$. Then $J$ has a common zero in $K^n$: there is $a \in K^n$ with
--   $$f(a) = 0 \quad \text{for all } f \in J.$$
--
--   This is the "zero" in the name *Nullstellensatz*: a proper ideal always has a point.
--
--   **Formalization Note.** $K$ is a $k$-algebra (the embedding $k \to K$ is part of the data) and $f(a)$ is evaluation of $f \in k[X]$ at $a \in K^n$ through that embedding.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 3 (weak Nullstellensatz).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem weak_nullstellensatz {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {n : ℕ} (J : Ideal (MvPolynomial (Fin n) k)) (hJ : J ≠ ⊤) :
    ∃ a : Fin n → K, ∀ f ∈ J, aeval a f = 0 := by sorry

end Nullstellensatz
