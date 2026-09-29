-- Prove2me | Theorems.Thm_InverseGalois_inverse_galois_problem_symmetric_group
-- name    : InverseGalois.inverse_galois_problem_symmetric_group
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T02:12:12.70142+00:00
-- url     : https://prove2.me/theorems/d7730635-8686-4eaa-9781-2adb740ab800
-- title:
--   Symmetric groups are realizable over $\mathbb{Q}$
-- statement:
--   For every finite type $S$, the symmetric group $\mathrm{Sym}(S)$ of all permutations of $S$ is the Galois group of a Galois extension of $\mathbb{Q}$.
--
--   Taking $S$ with $n$ elements, this says that $S_n$ is realizable over $\mathbb{Q}$ for every $n$, a theorem of Hilbert. The degenerate cases are included: for $S$ empty or a singleton, $\mathrm{Sym}(S)$ is trivial and the statement is realized by the extension $\mathbb{Q}/\mathbb{Q}$.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem inverse_galois_problem_symmetric_group
    {S : Type*} [Fintype S] :
    IsRealizable ℚ (Equiv.Perm S) := by sorry

end InverseGalois
