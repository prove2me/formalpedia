-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom
-- name    : GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/db1a640f-6c2b-533b-93b0-3118e5944543
-- title:
--   Homomorphic endomorphism restricts uniquely to the n-torsion kernel
-- statement:
--   Let $R$ be a commutative ring, $J$ a scheme and $f\colon J\to\operatorname{Spec} R$, and let $L$ be a relative group law on $f$: a group structure, functorial in the base, on the sets $\operatorname{SchemeHomOver} t\,f=\{\varphi\colon T\to J\mid \varphi\circ f=t\}$ of points of $J$ over each $t\colon T\to\operatorname{Spec} R$, given by operations `mul`, `one`, `inv` satisfying associativity, the unit laws, left inversion and naturality under base change. Assume `mul` is commutative for all $T$. Let $n\in\mathbb{N}$ and let $\varphi\colon J\to J$ satisfy $\varphi\circ f=f$ and be a homomorphism on points: $(L.\mathrm{mul}\,t\,x\,y)$ followed by $\varphi$ equals $L.\mathrm{mul}\,t$ of $x$ followed by $\varphi$ and $y$ followed by $\varphi$, for all $t$ and all $x,y$. Write $[n]=L.\mathrm{schemeNsmul}\,n\colon J\to J$, the underlying morphism of the $n$-fold $L$-sum of the identity point, $e\colon\operatorname{Spec} R\to J$ for the unit point over the identity, $K$ for the pullback of $[n]$ along $e$ and $\mathrm{pr}_1\colon K\to J$ for its first projection, so that $K$ carries the structure morphism $\mathrm{pr}_1$ followed by $f$. Then there is a morphism $e_K\colon K\to K$ over $\operatorname{Spec} R$ (i.e. compatible with $\mathrm{pr}_1\circ f$) with $\mathrm{pr}_1\circ e_K=\varphi\circ\mathrm{pr}_1$; it is the unique such morphism; and for every relative group law $L_K$ on $\mathrm{pr}_1$ followed by $f$ for which the point $\mathrm{pr}_1$ of $J$ over $K$ is a homomorphism (composing an $L_K$-product with $\mathrm{pr}_1$ gives the $L$-product of the composites, for all bases and pairs of points), $e_K$ is a homomorphism for $L_K$: composing an $L_K$-product with $e_K$ gives the $L_K$-product of the composites, for every $s\colon T\to\operatorname{Spec} R$ and all points $x,y$ of $K$ over $s$.
--
--   This is the functorial statement that an endomorphism of a commutative group law which respects the group structure on points preserves the $n$-torsion kernel, restricting to it uniquely and again homomorphically. It is used in the construction of Hecke-algebra idempotents acting on torsion kernels attached to the Néron identity component of the Jacobian of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (φ : SchemeHomOver f f)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        L.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    ∃ eK : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f),
      eK.1 ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ.1 ∧
      (∀ eK' : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f),
        eK'.1 ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ.1 → eK' = eK) ∧
      (∀ (LK : RelativeGroupLaw R (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
        (∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
          NeronModelInfra.schemeHomOverComp (LK.mul s x y)
              (⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩ : SchemeHomOver (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) f) =
            L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)
              (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1, rfl⟩)) →
        ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f)),
          NeronModelInfra.schemeHomOverComp (LK.mul s x y) eK =
            LK.mul s (NeronModelInfra.schemeHomOverComp x eK) (NeronModelInfra.schemeHomOverComp y eK)) := by sorry
