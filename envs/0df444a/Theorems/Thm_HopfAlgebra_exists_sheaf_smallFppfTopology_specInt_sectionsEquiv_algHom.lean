-- Prove2me | Theorems.Thm_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom
-- name    : HopfAlgebra.exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/4c0fab7e-c24d-5a32-949c-5c21a7ee1e4b
-- title:
--   Points of a ℤ-Hopf algebra as an fppf sheaf
-- statement:
--   Let $H$ be a commutative ring in `Type` equipped with the structure of a Hopf algebra over $\mathbf Z$, and assume the hypothesis `hcomm`: for every commutative ring $A$ the convolution product on $\mathbf Z$-algebra homomorphisms $H \to A$ (the multiplication carried by `WithConv (H →ₐ[ℤ] A)`) is commutative, i.e. $f * g = g * f$ for all such $f,g$. Write `specInt` for $\operatorname{Spec}\mathbf Z$ and let `specInt.Fppf` be the small fppf site over it: its objects are schemes $U.\mathrm{left}$ together with a morphism to $\operatorname{Spec}\mathbf Z$ that is flat and locally of finite presentation, its morphisms are morphisms over $\operatorname{Spec}\mathbf Z$, and `smallFppfTopology specInt` is the associated small Grothendieck topology. The conclusion asserts the existence of a sheaf $\mathcal J$ of abelian groups on this site, together with, for every object $U$, an isomorphism of additive groups $e_U$ from $\mathcal J(U)$ to the additive group `Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤)))`, that is, to the group of $\mathbf Z$-algebra maps $H \to \Gamma(U.\mathrm{left}, \mathcal O)$ under convolution, subject to the following compatibility: for every morphism $f : U \to V$ of the site, every section $s \in \mathcal J(V)$ and every $h \in H$, the algebra map $e_U$ of the restriction of $s$ along $f$ sends $h$ to the image under $\Gamma(f.\mathrm{left})$ of the value at $h$ of the algebra map $e_V(s)$.
--
--   This is the statement that the functor of points of the affine group scheme $\operatorname{Spec}H$ over $\operatorname{Spec}\mathbf Z$, with its convolution group law, is an abelian sheaf on the small fppf site of $\operatorname{Spec}\mathbf Z$, the group structure being abelian by the cocommutativity hypothesis `hcomm` imposed on points. It supplies the sheaf-with-sections data used in the construction of the primary torsion core of the Néron model of the Jacobian $J_0$ and in the associated level maps and embeddings of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

theorem HopfAlgebra.exists_sheaf_smallFppfTopology_specInt_sectionsEquiv_algHom
    (H : Type) [CommRing H] [HopfAlgebra ℤ H]

    (hcomm : ∀ (A : Type) [CommRing A] (f g : WithConv (H →ₐ[ℤ] A)), f * g = g * f) :
    ∃ (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
      (e : ∀ U : specInt.Fppf,
        𝒥.1.obj (Opposite.op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤)))),
      ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (Opposite.op V)) (h : H),
        (Additive.toMul (e U (𝒥.1.map f.op s))) h
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) h) := by sorry
