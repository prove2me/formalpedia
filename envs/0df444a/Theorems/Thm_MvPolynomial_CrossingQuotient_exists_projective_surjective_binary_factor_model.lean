-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_exists_projective_surjective_binary_factor_model
-- name    : MvPolynomial.CrossingQuotient.exists_projective_surjective_binary_factor_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T22:14:41.474002+00:00
-- url     : https://prove2.me/theorems/531b8729-e3ef-409f-a060-dc1b9f2c6dcd
-- title:
--   A projective surjective binary nodal factorization with explicit affine charts
-- statement:
--   Let $R$ be any commutative ring, let $a,b\in R$, and put $N(c)=\operatorname{Spec}R[x,y]/(xy-c)$. There is a scheme $X$ with a proper surjective morphism $q:X\to N(ab)$ and two jointly covering affine open charts $N(a)\hookrightarrow X$, $N(b)\hookrightarrow X$.
--
--   Write $(u,z)$ for the coordinates on $N(a)$ and $(w,v)$ for those on $N(b)$. The maps to $N(ab)$ are
--   $$ (u,z)\longmapsto(u,bz),\qquad(w,v)\longmapsto(aw,v). $$
--   Their actual scheme-theoretic intersection is $D(z)\subset N(a)$, identified with $D(w)\subset N(b)$ by $w=z^{-1}$ and $v=bz$. The statement retains both open immersions, their joint covering property, the exact coordinate homomorphisms and the actual cartesian overlap square.
--
--   Moreover this same scheme $X$ has a closed embedding into the relative projective line over $N(ab)$:
--   $$e:X\hookrightarrow\mathbb P^1_{N(ab)},\qquad \pi\circ e=q.$$
--   Thus the specific covering morphism $q$ is projective, with an explicit one-dimensional projective ambient space over the original node. No domain, noetherian, regularity, discrete-valuation or nonvanishing assumption is made on $R,a,b$. Regularity of $X$ and global boundary resolution are separate assertions.
-- source:
--   Binary local factorization underlying A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 3.6, pp. 64-65; https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . Taking a=t_1 and b=t_2...t_l gives the two local equations in that resolution step. This arbitrary-ring formulation with its explicit relative P1 embedding is a derived auxiliary theorem, not a verbatim numbered assertion. The closed embedding is checked on both standard charts of P1 using their homogeneous-localization coordinate rings; surjectivity follows by lifting each residue-field point into a chart. No blowup identification, chart regularity or global alteration is asserted.

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem MvPolynomial.CrossingQuotient.exists_projective_surjective_binary_factor_model {R : Type u} [CommRing R] (a b : R) :
    ∃ (X : Scheme.{u}) (q : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
      (i : Spec (.of (CrossingQuotient R a)) ⟶ X)
      (j : Spec (.of (CrossingQuotient R b)) ⟶ X)
      (α : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R a)
      (β : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R b)
      (θ : CrossingQuotient R b →ₐ[R] Localization.Away (V a)),
      IsProper q ∧ Surjective q ∧ IsOpenImmersion i ∧ IsOpenImmersion j ∧
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
          (algebraMap (CrossingQuotient R a) (Localization.Away (V a))))) j i ∧
      ∃ e : X ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) (CrossingQuotient R (a * b))
        (@CommRing.toCommSemiring (CrossingQuotient R (a * b)) inferInstance)),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π (CrossingQuotient R (a * b)) 1 = q := by sorry
