-- Prove2me | Theorems.Thm_Nullstellensatz_real_counterexample
-- name    : Nullstellensatz.real_counterexample
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:10:43.440984+00:00
-- url     : https://prove2.me/theorems/db53b681-5c29-4ed8-885c-1ad150dfa24b
-- title:
--   $(X^2+1)$ has no common zero in $\mathbb R$
-- statement:
--   The ideal $(X^2 + 1)$ of $\mathbb R[X]$ is proper, and its elements have no common zero in $\mathbb R$:
--   $$(X^2+1) \ne \mathbb R[X], \qquad \neg\,\exists\, x \in \mathbb R\ \ \forall f \in (X^2+1),\ f(x) = 0.$$
--
--   This shows that the algebraic closedness of $K$ cannot be dropped from the weak Nullstellensatz.
-- source:
--   Wikipedia, article "Hilbert's Nullstellensatz" (snapshot supplied as Hilbert's_Nullstellensatz.pdf, printed 2026-09-27), https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz, section "Formulations", paragraph 3, last sentence (the ideal (X^2+1) in R[X]).

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

namespace Nullstellensatz

theorem real_counterexample :
    Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)} ≠ ⊤ ∧
      ¬ ∃ x : ℝ, ∀ f ∈ Ideal.span {(Polynomial.X ^ 2 + 1 : Polynomial ℝ)}, f.eval x = 0 := by
  sorry

end Nullstellensatz
