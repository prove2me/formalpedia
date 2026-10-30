-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_exists_smooth_integral_projective_cover_of_monomial
-- name    : MvPolynomial.CrossingQuotient.exists_smooth_integral_projective_cover_of_monomial
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-29T14:41:24.667858+00:00
-- url     : https://prove2.me/theorems/79d087d7-23e7-42f3-8278-664c95c82441
-- title:
--   Smooth integral projective covers of arbitrary monomial nodes
-- statement:
--   Let $K$ be a commutative integral domain, let $I$ be a finite set of variables, and let $(d_i)_{i\in I}$ be nonnegative integer exponents. Set
--   $$N_d=\operatorname{Spec}\bigl(K[(t_i)_{i\in I},u,v]/(uv-\prod_{i\in I}t_i^{d_i})\bigr).$$
--   There exist an integral scheme $Y$ and a proper surjective morphism $q:Y\to N_d$ such that the composite of $q$ with the original coefficient structure map to $\operatorname{Spec}K$ is smooth. This same covering morphism is projective: for some integer $n\geq0$ there is a closed immersion
--   $$j:Y\hookrightarrow\mathbb P^n_{N_d},\qquad \pi\circ j=q.$$
--   Moreover the complete restriction over $D(u)$ is an isomorphism:
--   $$q^{-1}(D(u))\xrightarrow{\sim}D(u).$$
--   Zero exponents, the unit monomial and the empty variable set are included. No field, characteristic, perfectness, noetherianity or regularity assumption on $K$ is imposed.
--
--   This gives a projective cover of the affine polynomial monomial-node model with smooth integral source. Compatible modifications on overlapping etale charts and alterations of arbitrary global families remain additional assertions.
-- source:
--   Derived affine polynomial-base projective monomial-node construction motivated by A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathematiques de l’IHES 83 (1996), Sections 3.3–3.6, pp. 63–65; https://www.numdam.org/article/PMIHES_1996__83__51_0.pdf . This is an auxiliary local projective-cover theorem, not a verbatim numbered assertion. The actual right-chart replacement has a closed graph in a finite product of projective lines over the original coefficient ring. The induction retains the whole D(u) section and normalized initial-product projective coordinates, so all coordinates extend across the unchanged first chart. Existing Proved finite-product and projective base-change theorems give a single relative projective embedding on that same covering scheme. No blowup identification, compatible descent across etale overlaps or global alteration is asserted.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem MvPolynomial.CrossingQuotient.exists_smooth_integral_projective_cover_of_monomial
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ) :
    let R := MvPolynomial σ K
    let c : R := MvPolynomial.monomial d 1
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (CrossingQuotient R c))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap R (CrossingQuotient R c)).comp (MvPolynomial.C : K →+* R)))) ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U c)) ∧
      ∃ (N : ℕ) (j : Y ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (N + 1))
        (CrossingQuotient R c) (@CommRing.toCommSemiring (CrossingQuotient R c) inferInstance))),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π (CrossingQuotient R c) N = q := by sorry
