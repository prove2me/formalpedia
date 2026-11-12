-- Prove2me | Theorems.Thm_InverseGalois_regular_inverse_galois_symmetric
-- name    : InverseGalois.regular_inverse_galois_symmetric
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-09-13T17:28:55.148666+00:00
-- url     : https://prove2.me/theorems/67b1290d-c95d-4324-8829-c9ec4a5896f6
-- title:
--   Symmetric groups are realizable over $\mathbb{Q}(t)$
-- statement:
--   For every finite type $S$, the symmetric group $\mathrm{Sym}(S)$ is the Galois group of a Galois extension of the rational function field $\mathbb{Q}(t)$.
--
--   This is the **geometric half** of Hilbert's theorem that $S_n$ is realizable over $\mathbb{Q}$. Classically, the generic polynomial
--   $$ X^n + a_{n-1}X^{n-1} + \cdots + a_0 $$
--   has Galois group $S_n$ over the field $\mathbb{Q}(a_0,\dots,a_{n-1})$ of rational functions in its coefficients, since the elementary symmetric functions are algebraically independent. Specializing all but one of the parameters, in such a way that the Galois group is preserved, realizes $S_n$ over a rational function field $\mathbb{Q}(t)$ in a single variable; such a realization is called *regular*.
--
--   Combined with the specialization step supplied by Hilbert's irreducibility theorem (the milestone `InverseGalois.inverse_galois_problem_hilbert_descent`), this yields realizability of $\mathrm{Sym}(S)$ over $\mathbb{Q}$ itself.
--
--   The degenerate cases are included: for $S$ empty or a singleton, $\mathrm{Sym}(S)$ is trivial and the statement is realized by the trivial extension.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026), section 'Symmetric and alternating groups'; regular realizations over Q(t) and Hilbert irreducibility as in Serre, Topics in Galois Theory, ch. 1-3

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem regular_inverse_galois_symmetric
    {S : Type*} [Fintype S] :
    IsRealizable (RatFunc ℚ) (Equiv.Perm S) := by sorry

end InverseGalois
