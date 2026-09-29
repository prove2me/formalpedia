-- Prove2me | Theorems.Thm_Garrido_exists_orderOf_eq_two_pow
-- name    : Garrido.exists_orderOf_eq_two_pow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T13:10:33.594571+00:00
-- url     : https://prove2.me/theorems/109ad009-6c74-4950-9468-8a24d386b485
-- title:
--   Proposition 4.7 — every element of Γ has order a power of 2
-- statement:
--   Every element of $\Gamma$ has finite order, and that order is a power of $2$:
--
--   $$\forall g \in \Gamma\ \exists k \ge 0 : \ \operatorname{ord}(g) = 2^k.$$
--
--   So $\Gamma$ is an infinite, finitely generated torsion group.
--
--   **Formalization Note.** $\operatorname{ord}$ is Mathlib's `orderOf`, which is $0$ for an element
--   of infinite order; since $2^k \ge 1$, the statement also asserts that every order is finite.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 14, Proposition 4.7; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The source omits the proof and refers to P. de la Harpe, Topics in Geometric Group Theory, Chicago Lectures in Mathematics, University of Chicago Press (2000), Chapter VIII; https://press.uchicago.edu/ucp/books/book/chicago/T/bo3641370.html

import Mathlib
import Definitions.Def_Garrido_Grigorchuk

namespace Garrido

theorem exists_orderOf_eq_two_pow (g : GrigorchukGroup) : ∃ k : ℕ, orderOf g = 2 ^ k := by
  sorry

end Garrido
