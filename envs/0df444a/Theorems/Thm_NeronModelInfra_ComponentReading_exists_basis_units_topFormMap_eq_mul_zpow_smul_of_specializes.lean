-- Prove2me | Theorems.Thm_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
-- name    : NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/5dbd1e1f-0e58-5623-8067-882b3502a908
-- title:
--   Value of ω at an F-point specialising through y₁
-- statement:
--   Let $R$ be a discrete valuation domain with uniformiser $\varpi$, so that $\mathfrak m_R=(\varpi)$, let $K$ be a fraction field of $R$, and let $g_K\colon X_K\to\operatorname{Spec}K$ be smooth of relative dimension $d$. Let $\omega$ be a section of `gK.topDifferentials d` (the $d$-th determinant of the sheafified relative Kähler differentials of $g_K$) over $\top$ which is a frame there: for every open $W$, multiplication $g\mapsto g\cdot\omega|_W$ is a bijection $\Gamma(X_K,W)\to\Gamma(\mathrm{topDifferentials}\ d,W)$. Let $T$ be a `ComponentReading` for these data, consisting of a smooth, locally of finite type $R$-scheme $T.f\colon T.Y\to\operatorname{Spec}R$, an open immersion $T.e$ of the generic fibre $T.Y\times_{\operatorname{Spec}R}\operatorname{Spec}K$ into $X_K$ over $g_K$, a point $T.y$ over the closed point of $R$ maximal in the sense that any point over the closed point having $T.y$ as a specialisation equals $T.y$, with $\mathcal O_{T.Y,T.y}$ a discrete valuation ring and an $R$-algebra compatibly with $T.f$, a basis $T.b$ of $\Omega_{\mathcal O_{T.Y,T.y}/R}$, an affine open $T.U\subseteq X_K$, and further fields comparing $\omega$ with $T.b$ and fixing the integer $T.n$. Let $y_1$ be a point of $T.Y$ over the closed point of $R$ which is a specialisation of $T.y$, and equip $\mathcal O_1:=\mathcal O_{T.Y,y_1}$ with an $R$-algebra structure such that `T.Y.fromSpecStalk y₁` followed by $T.f$ is $\operatorname{Spec}$ of $R\to\mathcal O_1$. Let $F$ be a field which is an algebra over $\mathcal O_1$, over $R$ and over $K$, with $R\to\mathcal O_1\to F$ and $R\to K\to F$ scalar towers, let $U\subseteq X_K$ be an affine open with an algebra map $\Gamma(X_K,U)\to F$ forming a scalar tower over the $K$-algebra structure `gK.sectionsAlgebra U` on $\Gamma(X_K,U)$, and assume the induced $\operatorname{Spec}F\to\operatorname{Spec}\Gamma(X_K,U)\to X_K$ equals the $F$-point obtained by transporting $\operatorname{Spec}\mathcal O_1\to T.Y$ into the generic fibre and composing with $T.e$. Finally let $\omega_U\in\bigwedge^d_{\Gamma(X_K,U)}$ of `gK.kaehlerPresheaf` at $U$ satisfy `gK.topToSections d U ωU` $=\omega|_U$. Then there are a basis $b'$ of $\Omega_{\mathcal O_1/R}$ indexed by $\mathrm{Fin}\,d$ and a unit $w\in\mathcal O_1^\times$ with $$\mathrm{topFormMap}_{K,K,\Gamma(X_K,U),F}\,\omega_U=\bigl(w_F\cdot(\varpi_F)^{T.n}\bigr)\cdot\mathrm{topFormMap}_{R,K,\mathcal O_1,F}\,(b'_1\wedge\dots\wedge b'_d)$$ in $\bigwedge^d_F\Omega_{F/K}$, where the subscript $F$ denotes the images in $F$ and the power is taken with the integer $T.n$.
--
--   This is the computation of the value of a global frame $\omega$ at an $F$-valued point of $X_K$ factoring through the stalk at a specialisation $y_1$ of the maximal point of a reading $T$: up to a unit it is $\varpi^{n(T)}$ times a wedge of a basis of $\Omega_{\mathcal O_{Y,y_1}/R}$, with the exponent the invariant $T.n$ attached to $T$ and in particular independent of $F$, $U$ and $\omega_U$. It feeds the comparison of orders between two readings and the statement identifying $n$ with formal smoothness of the stalk, in the construction of weak Néron models underlying the order-theoretic step of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_ComponentReading_exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_NeronModelInfra_OmegaMinimalComponentData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁))))
    (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
    [IsScalarTower R (T.Y.presheaf.stalk y₁) F] [IsScalarTower R K F]
    (U : XK.Opens) (hU : IsAffineOpen U) [Algebra Γ(XK, U) F]
    (hKU : letI := gK.sectionsAlgebra U; IsScalarTower K Γ(XK, U) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) F)) ≫ hU.fromSpec =
      (schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk y₁, halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
        T.e).1)
    (ωU : ⋀[Γ(XK, U)]^d (gK.kaehlerPresheaf.obj (op U)))
    (hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    ∃ (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
      (w : (T.Y.presheaf.stalk y₁)ˣ),
      letI := gK.sectionsAlgebra U
      TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
        (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
            algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ T.n) •
          TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
            (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b') := by sorry
