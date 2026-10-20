-- Prove2me | Theorems.Thm_Milne_zeta_p1
-- name    : Milne.zeta_p1
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-20T03:13:15.906836+00:00
-- url     : https://prove2.me/theorems/94dca92a-5e36-4ba0-8619-00be23715718
-- title:
--   The zeta function of the projective line is the reciprocal of (1 − t)(1 − p t)
-- statement:
--   A variety with 1 + p^m points over the field with p^m elements has zeta function Z(X, t) = 1/((1 − t)(1 − p t)): the Taylor coefficients of the zeta function attached to the count sequence m ↦ 1 + p^m are the partial geometric sums 1 + p + ⋯ + p^n (Section 7 of the source: Z(P¹, t) = 1/((1 − t)(1 − p t))).
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 7 (p. 10): Z(P¹, t) = 1/((1 − t)(1 − p t)).

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta

namespace Milne

/-- The zeta function of the projective line (section 7 of the paper): a
variety with 1 + p^m points over the field with p^m elements has zeta
function Z(X, t) = 1/((1 − t)(1 − pt)); the Taylor coefficients of the
zeta function attached to the count sequence m ↦ 1 + p^m are the
partial geometric sums Σ_{k=0}^{n} p^k. -/
theorem zeta_p1 (p : ℕ) (n : ℕ) :
    zetaCoeff (fun m => (1 : ℚ) + (p : ℚ) ^ m) n
      = ∑ k ∈ Finset.range (n + 1), (p : ℚ) ^ k := by
  sorry

end Milne
