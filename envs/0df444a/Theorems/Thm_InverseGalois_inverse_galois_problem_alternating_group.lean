-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_alternating_group
-- name    : InverseGalois.inverse_galois_problem_alternating_group
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:12:36.315952+00:00
-- url     : https://prove2.me/theorems/4c5bcf2b-2c69-435c-aa8c-7df4f8bb558e
-- title:
--   Alternating groups are realizable over $\mathbb{Q}$
-- statement:
--   For every natural number $n$, the alternating group $A_n$ — the subgroup of even permutations of an $n$-element set — is the Galois group of a Galois extension of $\mathbb{Q}$.
--
--   This is Hilbert's theorem for alternating groups. Small $n$ is included: for $n \le 1$ the group $A_n$ is trivial.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_alternating_group (n : ℕ) :
    IsRealizable ℚ (alternatingGroup (Fin n)) := by sorry

end InverseGalois
