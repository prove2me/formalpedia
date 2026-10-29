-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_exists_smooth_integral_proper_cover_of_monomial
-- name    : MvPolynomial.CrossingQuotient.exists_smooth_integral_proper_cover_of_monomial
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-29T01:35:37.921493+00:00
-- url     : https://prove2.me/theorems/5b605de5-d892-4596-b119-76ba187fb468
-- title:
--   Smooth integral proper covers of arbitrary monomial nodes
-- statement:
--   Let $K$ be a commutative integral domain, let $I$ be a finite set of variables, and let $d=(d_i)_{i\in I}$ be a vector of nonnegative integer exponents. Put
--   $$N_d=\operatorname{Spec}\bigl(K[(t_i)_{i\in I},u,v]/(uv-\prod_{i\in I}t_i^{d_i})\bigr).$$
--   There exist an integral scheme $Y$ and a proper surjective morphism
--   $$q:Y\longrightarrow N_d$$
--   whose composite with the original structure map to $\operatorname{Spec}K$ is smooth. The complete restriction of $q$ over the principal open $D(u)$ is an isomorphism:
--   $$q^{-1}(D(u))\xrightarrow{\sim}D(u).$$
--   Zero exponents, the unit monomial and the empty variable set are included. No field, characteristic, perfectness, noetherianity or regularity assumption on $K$ is required.
--
--   This is the affine monomial form of the local cover used in nodal boundary constructions. Compatible global projective modifications and alterations of arbitrary families remain additional assertions.
-- source:
--   Derived affine polynomial-base local case of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 3.3, p. 63 (the monomial nodal local equation), and the two affine factor charts in the proof of Proposition 3.6, p. 65; https://www.numdam.org/article/PMIHES_1996__83__51_0.pdf . This is an auxiliary proper-cover theorem, not a verbatim numbered assertion. The proof eliminates the chosen polynomial variable in each first chart and glues an inductive cover of the second chart using an actual identity-overlap pullback. Relative smoothness over arbitrary coefficient domains follows from the explicit polynomial coordinate isomorphisms. The iterated cover is asserted proper, surjective and unchanged over D(u); global relative projectivity and a blowup identification are not asserted.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
universe u

theorem MvPolynomial.CrossingQuotient.exists_smooth_integral_proper_cover_of_monomial
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ) :
    let R := MvPolynomial σ K
    let c : R := MvPolynomial.monomial d 1
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (CrossingQuotient R c))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap R (CrossingQuotient R c)).comp (MvPolynomial.C : K →+* R)))) ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U c)) := by sorry
