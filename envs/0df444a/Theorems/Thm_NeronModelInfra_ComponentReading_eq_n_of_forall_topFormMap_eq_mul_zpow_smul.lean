-- Prove2me | Theorems.Thm_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul
-- name    : NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c22efe71-8806-5f74-b19e-0d74bef510d3
-- title:
--   Local exponent of ω at a closed-fibre point equals T.n
-- statement:
--   Let $R$ be a discrete valuation domain with uniformiser $\varpi$, so that its maximal ideal is $(\varpi)$, let $K$ be a fraction field of $R$, and let $g_K : X_K \to \operatorname{Spec} K$ be smooth of relative dimension $d$. Let $\omega$ be a global section of the $d$-th determinant $g_K$-module `gK.topDifferentials d` of the relative Kähler module of $g_K$ which is a frame on all of $X_K$: for every open $W$, multiplication $g \mapsto g\cdot \omega|_W$ is a bijection $\Gamma(X_K,W) \to \Gamma(\mathrm{top}, W)$. Let $T$ be a `ComponentReading R K gK d ω`, which bundles a smooth, locally of finite type $R$-scheme $T.Y \to \operatorname{Spec} R$, an open immersion $T.e$ of the generic fibre of $T.f$ into $X_K$ over $\operatorname{Spec} K$, a point $T.y$ of the closed fibre maximal among its own specialisations with discrete valuation stalk, a basis $T.b$ of $\Omega_{\mathcal O_{T.Y,T.y}/R}$, an affine chart $T.U$ of $X_K$ with its data, and an integer $T.n$. Let $y_1 \in T.Y$ lie over the closed point of $R$ with $T.y \rightsquigarrow y_1$, write $\mathcal O_1 = \mathcal O_{T.Y,y_1}$, and fix an $R$-algebra structure on $\mathcal O_1$ for which $\operatorname{Spec} \mathcal O_1 \to T.Y \to \operatorname{Spec} R$ is induced by $R \to \mathcal O_1$. Let $b'$ be a basis of $\Omega_{\mathcal O_1/R}$ indexed by $\mathrm{Fin}\ d$, let $w \in \mathcal O_1^\times$ and $m \in \mathbb Z$. Assume: for every field $F$ that is an algebra over $\mathcal O_1$, over $R$ and over $K$ with the towers $R \to \mathcal O_1 \to F$ and $R \to K \to F$ compatible, every affine open $U \subseteq X_K$ with an $F$-algebra structure on $\Gamma(X_K,U)$ compatible with $K \to \Gamma(X_K,U)$ coming from $g_K$, such that the resulting $F$-point $\operatorname{Spec} F \to \operatorname{Spec}\Gamma(X_K,U) \to X_K$ is the $F$-point obtained from $\operatorname{Spec}\mathcal O_1 \to T.Y$ by passing to the generic fibre and composing with $T.e$, and every $\omega_U \in \bigwedge^d_{\Gamma(X_K,U)} \Omega_{\Gamma(X_K,U)/K}$ whose image under `gK.topToSections d U` is the restriction of $\omega$ to $U$, the base change of $\omega_U$ to $\bigwedge^d \Omega_{F/K}$ equals $w\,\varpi^{m}$ (images in $F$) times the base change of $db'_1 \wedge \dots \wedge db'_d$. The conclusion is $m = T.n$.
--
--   This is the uniqueness half of the statement that the order of the invariant top form $\omega$ along a component of the closed fibre is well defined: any exponent read off from a local Laurent expression of $\omega$ at a point $y_1$ of the closed fibre to which the distinguished point $T.y$ specialises is forced to be the integer $T.n$ carried by the reading $T$. It is used by [`NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes`](thm.html#NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes), where such a local expression is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_ComponentReading_eq_n_of_forall_topFormMap_eq_mul_zpow_smul.lean

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

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open NeronModelInfra
open GoodReductionJacobian

universe u

theorem NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul
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
    (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
    (w : (T.Y.presheaf.stalk y₁)ˣ) (m : ℤ)
    (h : ∀ (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
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
        (hωU : gK.topToSections d U ωU = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω),
        letI := gK.sectionsAlgebra U
        TopFormOrder.topFormMap K K Γ(XK, U) F d ωU =
          (algebraMap (T.Y.presheaf.stalk y₁) F (w : (T.Y.presheaf.stalk y₁)) *
              algebraMap (T.Y.presheaf.stalk y₁) F (algebraMap R (T.Y.presheaf.stalk y₁) ϖ) ^ m) •
            TopFormOrder.topFormMap R K (T.Y.presheaf.stalk y₁) F d
              (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b')) :
    m = T.n := by sorry
