-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_exists_smooth_integral_projective_two_parameter_cover
-- name    : MvPolynomial.CrossingQuotient.exists_smooth_integral_projective_two_parameter_cover
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-28T17:04:55.663543+00:00
-- url     : https://prove2.me/theorems/9b052149-8c05-4a61-a2c1-3c123fcee9f5
-- title:
--   A smooth integral projective cover of the two-parameter node uv=st
-- statement:
--   Let $K$ be any commutative integral domain, let $R=K[s,t]$, and let
--   $$N=\operatorname{Spec}\bigl(K[s,t,u,v]/(uv-st)\bigr).$$
--   There exist an integral scheme $Y$ and a proper surjective morphism $q:Y\to N$ such that $Y$ is smooth over $K$, with the structure morphism given by $q$ followed by the original projection $N\to\operatorname{Spec}K$.
--
--   The same scheme $Y$ admits a closed immersion into the relative projective line over $N$:
--   $$e:Y\hookrightarrow\mathbb P^1_N,\qquad \pi\circ e=q.$$
--   Thus the particular covering morphism $q$ is projective, with a specified relative projective ambient space. No field, perfectness, characteristic, noetherianity or regularity hypothesis on $K$ is required. The result concerns relative projectivity over the affine node $N$; it does not assert that $Y$ is proper over $K$.
--
--   This is the two-independent-parameter local case of the nodal boundary-cover construction. General monomial boundary charts and a globally compatible smooth cover remain separate assertions.
-- source:
--   Auxiliary two-parameter polynomial-chart case of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 3.6, pp. 64-65; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . This is a derived local cover theorem for uv=st, not a verbatim numbered assertion. It reuses the Proved arbitrary-ring projective binary factorization https://prove2.me/theorems/531b8729-e3ef-409f-a060-dc1b9f2c6dcd and proves smoothness and integrality of its actual supplied charts and gluing. The result makes no blowup-identification or birationality assertion and does not construct stable moduli or a global alteration.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem MvPolynomial.CrossingQuotient.exists_smooth_integral_projective_two_parameter_cover (K : Type u) [CommRing K] [IsDomain K] :
    let R := Polynomial (Polynomial K)
    let s : R := Polynomial.X
    let t : R := Polynomial.C Polynomial.X
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (CrossingQuotient R (s * t)))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap R (CrossingQuotient R (s * t))).comp
          ((Polynomial.C : Polynomial K →+* R).comp
            (Polynomial.C : K →+* Polynomial K))))) ∧
      ∃ e : Y ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (1 + 1))
        (CrossingQuotient R (s * t))
        (@CommRing.toCommSemiring (CrossingQuotient R (s * t)) inferInstance)),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π (CrossingQuotient R (s * t)) 1 = q := by sorry
