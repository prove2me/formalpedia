-- Prove2me | Theorems.Thm_MetodosNumericos_horner_deflation
-- name    : MetodosNumericos.horner_deflation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T17:33:48.475256+00:00
-- url     : https://prove2.me/theorems/662bf061-7ee2-4a57-8f68-4bf405a385b7
-- title:
--   Deflation: $P(w) = (w-z)Q(w) + P(z)$ with Horner's coefficients
-- statement:
--   With $b_0, \\dots, b_n$ the Horner coefficients of $P$ at $z$, the polynomial $Q(w) = \\sum_{i=0}^{n-1} b_i w^{\\,n-1-i}$ satisfies $P(w) = (w-z)Q(w) + b_n$ for every $w$. In particular, when $z$ is a root, $Q$ is the deflated polynomial whose zeros are the remaining zeros of $P$.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 4, §4.7 Deflação de um Polinômio, pp. 81–82.

import Mathlib
import Definitions.Def_MetodosNumericos_polinomiosDefs

namespace MetodosNumericos

theorem horner_deflation (a : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (z w : ℝ) :
    polyVal a n w =
      (w - z) * (∑ i ∈ Finset.range n, hornerSeq a z i * w ^ (n - 1 - i)) + hornerSeq a z n := by
  sorry

end MetodosNumericos
