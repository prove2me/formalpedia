-- Prove2me | Theorems.Thm_InverseGalois_hilbert_descent_multivariate
-- name    : InverseGalois.hilbert_descent_multivariate
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-09-15T20:28:47.475463+00:00
-- url     : https://prove2.me/theorems/43b2360c-53d1-4931-8d11-f2ca3581c183
-- title:
--   Hilbert irreducibility: descent from $\mathbb{Q}(t_1,\dots,t_n)$ to $\mathbb{Q}$
-- statement:
--   Let $G$ be a finite group and let $I$ be a finite index set. If $G$ is the Galois group of some Galois extension of the rational function field $\mathbb{Q}(t_i : i \in I)$, then $G$ is the Galois group of some Galois extension of $\mathbb{Q}$.
--
--   This is the **arithmetic half** of Hilbert's method, and it packages two standard facts.
--
--   First, Hilbert's irreducibility theorem in its field-theoretic formulation: $\mathbb{Q}$ is a *Hilbertian* field, and if $K$ is Hilbertian then so is $K(t)$; consequently $\mathbb{Q}(t_1,\dots,t_n)$ is Hilbertian for every $n$.
--
--   Second, the specialization principle for Hilbertian fields: if $K$ is Hilbertian and $L/K(t)$ is a finite Galois extension with group $G$, then for all values $t = a \in K$ outside a thin set the specialized extension is Galois over $K$ with the same group $G$. Applying this once for each of the $n = |I|$ variables descends a realization of $G$ over $\mathbb{Q}(t_1,\dots,t_n)$ to one over $\mathbb{Q}(t_1,\dots,t_{n-1})$, and so on down to $\mathbb{Q}$.
--
--   The statement is a conditional one: it assumes realizability over the rational function field and concludes realizability over $\mathbb{Q}$. It is the several-variable form of the one-variable statement `InverseGalois.inverse_galois_problem_hilbert_descent`, and the several-variable form is what the *generic* realization of the symmetric and alternating groups needs, since the generic polynomial of degree $n$ has $n$ indeterminate coefficients.
--
--   In the formal statement the rational function field is presented as the fraction field of the polynomial ring over $\mathbb{Q}$ in variables indexed by a finite type $I$.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026), section 'Symmetric and alternating groups'; Serre, Topics in Galois Theory, ch. 3 (Hilbert's irreducibility theorem and specialization of Galois extensions of K(T)); Fried-Jarden, Field Arithmetic (3rd ed.), ch. 13 (Hilbertian fields: Q is Hilbertian and K Hilbertian implies K(t) Hilbertian)

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem hilbert_descent_multivariate
    {G : Type*} [Fintype G] [Group G] {I : Type} [Finite I]
    (h : IsRealizable (FractionRing (MvPolynomial I ℚ)) G) :
    IsRealizable ℚ G := by sorry

end InverseGalois
