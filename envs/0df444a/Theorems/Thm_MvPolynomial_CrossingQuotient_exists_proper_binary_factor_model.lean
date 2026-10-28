-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_exists_proper_binary_factor_model
-- name    : MvPolynomial.CrossingQuotient.exists_proper_binary_factor_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T21:08:54.779995+00:00
-- url     : https://prove2.me/theorems/9435251d-c63e-4cbd-8a17-207f5baab92e
-- title:
--   A proper two-chart factorization of a nodal product equation over an arbitrary commutative ring
-- statement:
--   Let $R$ be any commutative ring, let $a,b\in R$, and put $N(c)=\operatorname{Spec}R[x,y]/(xy-c)$. There is a scheme $X$ with a proper morphism $q:X\to N(ab)$ and two affine open charts $N(a)\hookrightarrow X$ and $N(b)\hookrightarrow X$ which jointly cover $X$.
--
--   In coordinates $(u,z)$ on $N(a)$ and $(w,v)$ on $N(b)$ the maps to $N(ab)$ are
--   $$ (u,z)\longmapsto(u,bz),\qquad (w,v)\longmapsto(aw,v). $$
--   Their actual scheme-theoretic intersection is $D(z)\subset N(a)$. Its map to $N(b)$ is $w=z^{-1}$, $v=bz$, identifying it with $D(w)\subset N(b)$. The conclusion includes the actual cartesian overlap square, both open immersions, the covering property, and the exact coordinate homomorphisms.
--
--   No domain, noetherian, discrete-valuation, regularity, or nonvanishing hypothesis is imposed on $R,a,b$. The theorem asserts properness of this explicit gluing; projectivity and regularity are separate assertions.
-- source:
--   Auxiliary binary nodal factorization underlying A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 3.6, pp. 64-65; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Specializing a=t_1 and b=t_2...t_l gives the two local equations used there. This arbitrary-ring formulation and the valuative proof are a derived auxiliary statement, not a verbatim numbered theorem. The separatedness and properness arguments use the affine diagonal criterion and the valuative criterion as implemented in Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474. The theorem does not identify the gluing with a blowup or assert that its charts are regular.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
universe u

theorem MvPolynomial.CrossingQuotient.exists_proper_binary_factor_model {R : Type u} [CommRing R] (a b : R) :
    ∃ (X : Scheme.{u}) (q : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
      (i : Spec (.of (CrossingQuotient R a)) ⟶ X)
      (j : Spec (.of (CrossingQuotient R b)) ⟶ X)
      (α : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R a)
      (β : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R b)
      (θ : CrossingQuotient R b →ₐ[R] Localization.Away (V a)),
      IsProper q ∧ IsOpenImmersion i ∧ IsOpenImmersion j ∧
      (∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x) ∧
      α (U (a * b)) = U a ∧ α (V (a * b)) = algebraMap R _ b * V a ∧
      β (U (a * b)) = algebraMap R _ a * U b ∧ β (V (a * b)) = V b ∧
      θ (U b) = IsLocalization.Away.invSelf (V a) ∧
      θ (V b) = algebraMap R _ b *
        algebraMap (CrossingQuotient R a) (Localization.Away (V a)) (V a) ∧
      i ≫ q = Spec.map (CommRingCat.ofHom α.toRingHom) ∧
      j ≫ q = Spec.map (CommRingCat.ofHom β.toRingHom) ∧
      IsPullback (Spec.map (CommRingCat.ofHom θ.toRingHom))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (CrossingQuotient R a) (Localization.Away (V a))))) j i := by sorry
