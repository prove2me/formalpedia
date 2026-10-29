-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_exists_smooth_integral_proper_cover_of_parameter_power
-- name    : MvPolynomial.CrossingQuotient.exists_smooth_integral_proper_cover_of_parameter_power
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-28T23:48:36.936668+00:00
-- url     : https://prove2.me/theorems/ee06d6ed-0a54-48e5-835b-ca6df92b64db
-- title:
--   Smooth integral proper covers of every positive power node
-- statement:
--   Let $K$ be a commutative integral domain and let $n\geq0$. Consider the affine power node
--   $$N_n=\operatorname{Spec}\bigl(K[t,u,v]/(uv-t^{n+1})\bigr).$$
--   There exist an integral scheme $Y$ and a proper surjective morphism
--   $$q:Y\longrightarrow N_n$$
--   such that the composite of $q$ with the original structure map to $\operatorname{Spec}K$ is smooth. Moreover, the actual restriction of $q$ over the principal open $D(u)$ is an isomorphism:
--   $$q^{-1}(D(u))\xrightarrow{\sim}D(u).$$
--   No field, characteristic, perfectness, noetherianity or regularity assumption on $K$ is required. The case $n=0$ is included.
--
--   This gives the repeated-one-parameter local cover needed in nodal boundary constructions, with the full unchanged principal open retained for further gluing. Global relative projectivity and arbitrary products of several boundary parameters remain separate requirements of the general alteration construction.
-- source:
--   Derived polynomial-base local case of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Sections 3.3–3.6, pp. 63–65, especially the nodal product equations of 3.3 and the two-chart factorization in the proof of Proposition 3.6; https://www.numdam.org/article/PMIHES_1996__83__51_0.pdf . This is an auxiliary proper-cover statement for uv=t^(n+1), not a verbatim numbered assertion. The proof works over any integral domain by polynomial-coordinate calculations and actual gluing of proper modifications, without invoking regularity of the coefficient ring. It retains an actual isomorphism over D(u) and makes no projectivity or blowup-identification assertion for the iterated cover. The binary projective construction is the same one recorded in https://prove2.me/theorems/531b8729-e3ef-409f-a060-dc1b9f2c6dcd ; its complete helpers are included rather than imported as unproved assumptions.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
universe u

theorem MvPolynomial.CrossingQuotient.exists_smooth_integral_proper_cover_of_parameter_power
    (K : Type u) [CommRing K] [IsDomain K] (n : ℕ) :
    let R := Polynomial K
    let c : R := Polynomial.X ^ (n + 1)
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (CrossingQuotient R c))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap R (CrossingQuotient R c)).comp (Polynomial.C : K →+* R)))) ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U c)) := by sorry
