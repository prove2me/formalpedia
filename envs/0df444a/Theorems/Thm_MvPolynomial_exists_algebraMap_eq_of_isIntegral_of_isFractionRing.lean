-- Prove2me | Theorems.Thm_MvPolynomial_exists_algebraMap_eq_of_isIntegral_of_isFractionRing
-- name    : MvPolynomial.exists_algebraMap_eq_of_isIntegral_of_isFractionRing
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:40:09.943608+00:00
-- url     : https://prove2.me/theorems/485b0cdc-7bf7-4bc0-84ed-4cb0091545ec
-- title:
--   The fraction field of a domain is algebraically closed in the fraction field of a polynomial ring over it
-- statement:
--   Let $A$ be an integral domain with field of fractions $K$, let $k \ge 0$, and let $K'$ be the field of fractions of the polynomial ring $A[y_1, \dots, y_k]$ in $k$ variables, regarded as an extension of $K$ compatibly with the maps $A \to K \to K'$ and $A \to A[y_1, \dots, y_k] \to K'$. Assume that $A[y_1, \dots, y_k]$ is integrally closed in $K'$ (for instance $A$ a unique factorisation domain such as $\mathbb{Z}$ or $\mathbb{F}_q[x_1, \dots, x_m]$). Then $K$ is algebraically closed in $K'$: every element $y \in K'$ that is integral over $K$ lies in the image of $K$, that is,
--
--   $$y = x \quad \text{for some } x \in K.$$
--
--   Geometrically, for $A = \mathbb{F}_q[x_1, \dots, x_m]$ this says that the projection $\mathbb{A}^{m+k} \to \mathbb{A}^m$ has a geometrically connected generic fibre; it is the input for the surjectivity of $\pi_1(\mathbb{A}^{m+k}) \to \pi_1(\mathbb{A}^m)$ in the homotopy exact sequence. Proof sketch: since $y$ is algebraic over $K = \operatorname{Frac} A$, there is $0 \neq c \in A$ with $c y$ integral over $A$, hence over $A[y_1, \dots, y_k]$, so $c y = P$ is a polynomial by integral closedness. Then $P$ is integral over $A$, and a polynomial over a domain that is integral over the coefficient ring is constant (compare degrees in a monic relation $p(P) = 0$ and induct on the number of variables), so $P = a \in A$ and $y = a / c \in K$.
--
--   Role: the surjective half of the homotopy sequence for the projection of affine spaces over a finite field.
--
--   **Formalization Note**: $A[y_1, \dots, y_k]$ is `MvPolynomial (Fin k) A`; the fraction fields are arbitrary fields `K`, `K'` with `IsFractionRing A K` and `IsFractionRing (MvPolynomial (Fin k) A) K'`, and the extension $K \to K'$ is an arbitrary `Algebra K K'` subject to the scalar towers `A → K → K'` and `A → MvPolynomial (Fin k) A → K'` (which determine it). Integral closedness is the hypothesis `IsIntegrallyClosed (MvPolynomial (Fin k) A)`, as in the source development (the conclusion itself holds for every domain $A$, since $K'$ is also the fraction field of the unique factorisation domain $K[y_1, \dots, y_k]$). All types live in one universe `u`. The statement is not vacuous: $A = \mathbb{Z}$, $K = \mathbb{Q}$, $K' = $ `FractionRing (MvPolynomial (Fin k) ℤ)` satisfies all hypotheses, and for $k \ge 1$ the field $K'$ contains elements outside $K$ (e.g. $y_1$), none of them integral over $K$.
-- source:
--   S. Lang, Algebra, revised 3rd ed., Springer GTM 211 (2002), Chapter VIII (transcendental extensions: a purely transcendental extension is regular, so its base field is algebraically closed in it); A. Grothendieck, SGA 1 (homotopy exact sequence of the etale fundamental group for a morphism with geometrically connected fibres)

import Mathlib

set_option autoImplicit false

universe u

theorem MvPolynomial.exists_algebraMap_eq_of_isIntegral_of_isFractionRing
    (A K K' : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (k : ℕ) [Field K'] [Algebra (MvPolynomial (Fin k) A) K'] [IsFractionRing (MvPolynomial (Fin k) A) K']
    [Algebra K K'] [Algebra A K'] [IsScalarTower A K K'] [IsScalarTower A (MvPolynomial (Fin k) A) K']
    [IsIntegrallyClosed (MvPolynomial (Fin k) A)] (y : K') (hy : IsIntegral K y) :
    ∃ x : K, algebraMap K K' x = y := by
  sorry
