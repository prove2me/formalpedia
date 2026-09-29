-- Prove2me | Theorems.Thm_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
-- name    : NeronModelInfra.ComponentReading.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/c5be006a-6c66-5c1b-9b9b-70eee7dbca96
-- title:
--   Laurent form of ω at a special point of a reading
-- statement:
--   Let $R$ be a discrete valuation domain, $\varpi \in R$ an element with $\mathfrak m_R = (\varpi)$, and $K$ an $R$-algebra which is a field and a fraction field of $R$. Let $g_K \colon X_K \to \operatorname{Spec} K$ be smooth of relative dimension $d$, and let $\omega$ be a global section of $g_K$'s top differentials $\det^d$ of the sheafified Kähler module, assumed to be a frame on $\top$: for every open $W$ the map $a \mapsto a \cdot (\omega|_W)$ from $\Gamma(X_K,W)$ to the sections of the top differentials over $W$ is bijective. Let $T$ be an $\omega$-reading in the sense of `ComponentReading R K gK d ω`, whose data include a smooth, locally of finite type $T.f \colon T.Y \to \operatorname{Spec} R$, an open immersion $T.e$ of the generic fibre $T.Y \times_{\operatorname{Spec} R} \operatorname{Spec} K$ into $X_K$ over $\operatorname{Spec} K$, a point $T.y$ over the closed point maximal among such specialisations, with discrete valuation stalk carrying an $R$-algebra structure compatible with $T.f$, a basis of $\Omega_{\mathcal O_{T.Y,T.y}/R}$ and an affine chart of $X_K$; the remaining fields are summarised here. Let $y_1 \in T.Y$ satisfy $T.f(y_1) =$ the closed point of $R$, with $T.y$ specialising to $y_1$, and equip $\mathcal O_1 := \mathcal O_{T.Y,y_1}$ with an $R$-algebra structure such that $\operatorname{Spec}\mathcal O_1 \to T.Y$ followed by $T.f$ is $\operatorname{Spec}$ of $R \to \mathcal O_1$. Then there are an $\mathcal O_1$-basis $b'$ of $\Omega_{\mathcal O_1/R}$ indexed by $\mathrm{Fin}\,d$, a unit $w \in \mathcal O_1^\times$ and an integer $m$ with the following property. For every field $F$ that is an algebra over $\mathcal O_1$, over $R$ and over $K$, with $R \to \mathcal O_1 \to F$ and $R \to K \to F$ compatible, every affine open $U \subseteq X_K$ with an algebra structure $\Gamma(X_K,U) \to F$ compatible with $K \to \Gamma(X_K,U)$ (the latter induced by $g_K$), such that the induced $F$-point $\operatorname{Spec} F \to \operatorname{Spec}\Gamma(X_K,U) \to X_K$ coincides with the $F$-point obtained from $\operatorname{Spec}\mathcal O_1 \to T.Y$ by passing to the generic fibre along $\mathcal O_1 \to F$, $K \to F$ and composing with $T.e$, and every $\omega_U$ in the $d$-th exterior power over $\Gamma(X_K,U)$ of the value at $U$ of the relative differentials presheaf of $g_K$ whose image under `topToSections` is the restriction of $\omega$ to $U$, one has, in $\bigwedge^d_F \Omega_{F/K}$, $$\mathrm{topFormMap}\,(\omega_U) = \bigl(w_F \cdot \varpi_F^{\,m}\bigr) \cdot \mathrm{topFormMap}\,(b'_1 \wedge \dots \wedge b'_d),$$ the two maps being the base-change maps $\bigwedge^d_{\Gamma(X_K,U)}\Omega_{\Gamma(X_K,U)/K} \to \bigwedge^d_F\Omega_{F/K}$ and $\bigwedge^d_{\mathcal O_1}\Omega_{\mathcal O_1/R} \to \bigwedge^d_F\Omega_{F/K}$, and $w_F, \varpi_F$ the images of $w$ and of $\varpi$ in $F$.
--
--   This is the existence half of the local reading of the invariant top form $\omega$ at a point of the closed fibre of a component reading: $\omega$ is expressed, uniformly in the test field $F$ and the affine chart used, as a unit times a power of the uniformiser times the wedge of a basis of $\Omega_{\mathcal O_1/R}$. It feeds the statement `exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes`, where the exponent $m$ is subsequently identified with the order attached to the component, as used in the weak Néron model computation of the measure of the set of integral points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_ComponentReading_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes.lean

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

theorem NeronModelInfra.ComponentReading.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    {d : ℕ} [SmoothOfRelativeDimension d gK]
    {ω : Γ(gK.topDifferentials d, ⊤)} (hω : Scheme.Modules.IsFrameOn ω ⊤)
    (T : ComponentReading R K gK d ω)
    (y₁ : ↥T.Y) (hy₁ : T.f.base y₁ = IsLocalRing.closedPoint R) (hgen : T.y ⤳ y₁)
    [Algebra R (T.Y.presheaf.stalk y₁)]
    (halg₁ : T.Y.fromSpecStalk y₁ ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) :
    ∃ (b' : Module.Basis (Fin d) (T.Y.presheaf.stalk y₁) (Ω[(T.Y.presheaf.stalk y₁)⁄R]))
      (w : (T.Y.presheaf.stalk y₁)ˣ) (m : ℤ),
      ∀ (F : Type u) [Field F] [Algebra (T.Y.presheaf.stalk y₁) F] [Algebra R F] [Algebra K F]
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
              (exteriorPower.ιMulti (T.Y.presheaf.stalk y₁) d b') := by sorry
