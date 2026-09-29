-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/05ec968d-89c7-5365-b270-67ea60b69ed6
-- title:
--   Homomorphic level maps factor through the embedded p^v-torsion
-- statement:
--   Fix a prime $p$, a nonzero $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$, and let $\Lambda$ be level data for $(p,M,H,Pl)$: in particular a scheme $X$, a morphism $f \colon X \to \operatorname{Spec}$ of the ring of rationals with denominator coprime to $p$, a relative group law $L$ on $f$, and the prescribed identifications of sections with the $J_H$-groups. Let $\sigma_p \colon \operatorname{Spec}\mathbb{F}_p \to$ that base be given, together with an $\mathbb{F}_p$-algebra structure on the base ring, and let $\mathcal{A}$ be a $p$-divisible group of height $h_\Lambda$ over the base ring. Assume given morphisms $\iota'_v \colon \operatorname{Spec}\bigl((\mathcal{A}\otimes\mathbb{F}_p).\mathrm{level}\,v\bigr) \to X \times_{\text{base}} \operatorname{Spec}\mathbb{F}_p$ for all $v$ which (i) lie over $\mathbb{F}_p$, (ii) are closed immersions, (iii) for each $v$ induce, via the lift into the fibre product of the endomorphism 'multiplication by $p^v$' of the base-changed group law with its unit section, an isomorphism onto that $p^v$-torsion kernel, and (iv) are homomorphic: for every commutative $\mathbb{F}_p$-algebra $B$ and points $x,y$ of $(\mathcal{A}\otimes\mathbb{F}_p)$ at level $v$ with values in $B$ whose composites with $\iota'_v$ lie over $\mathbb{F}_p$, the composite attached to the convolution product $xy$ is the group-law product of the two sections. Let further $\mathcal{G}$ be a $p$-divisible group of height $h$ over a commutative ring $Rh$ mapping to $\mathbb{F}_p$, let $v$ be fixed, and let $\varphi \colon \operatorname{Spec}(\mathbb{F}_p \otimes_{Rh} \mathcal{G}.\mathrm{level}\,v) \to X \times_{\text{base}} \operatorname{Spec}\mathbb{F}_p$ lie over $\mathbb{F}_p$ and be homomorphic in the same sense. Then there is a bialgebra homomorphism $\rho$ over $\mathbb{F}_p$ from $(\mathcal{A}\otimes\mathbb{F}_p).\mathrm{level}\,v$ to $(\mathcal{G}\otimes\mathbb{F}_p).\mathrm{level}\,v$ with $\operatorname{Spec}\rho$ followed by $\iota'_v$ equal to $\varphi$.
--
--   This is the lifting half of the statement that the finite flat group scheme $\operatorname{Spec}$ of a level of a $p$-divisible group, when mapped homomorphically into the special fibre of the level-$(M/p)$ model, lands in the $p^v$-torsion and does so by a map of bialgebras, the point being that the levels are not reduced, so geometric points do not suffice. It is used in the construction of the splitting of the special fibre of the Raynaud quotient, namely by [`ModularCurve.exists_bialgHom_levelTorsion_raynaudQuotient_baseChange_spec_comp_eq_of_finPtsWitness`](thm.html#ModularCurve.exists_bialgHom_levelTorsion_raynaudQuotient_baseChange_spec_comp_eq_of_finPtsWitness) and [`ModularCurve.specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness`](thm.html#ModularCurve.specMap_cokernel_comp_levelBaseChange_comp_abq_eq_one_of_finPtsWitness).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_BaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.JHNeronObjectAtP.LevelData.exists_bialgHom_specMap_comp_eq_of_isHom_baseChange_level
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ ModularCurve.JZeroNeronObjectAtP.base p)

    {hΛ : ℕ} (𝒜 : PDivisibleGroup (ModularCurve.JZeroNeronObjectAtP.baseRing p) p hΛ)
    [Algebra (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p)]
    (ι' : ∀ v : ℕ, Spec (CommRingCat.of ((𝒜.baseChange (ZMod p)).level v)) ⟶ pullback Λ.f σp)
    (hι'base : ∀ v : ℕ, ι' v ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))
    (hι'cl : ∀ v : ℕ, IsClosedImmersion (ι' v))
    (hι'p : ∀ (v : ℕ), ∃ h3 : ι' v ≫ (Λ.L.baseChange σp).schemeNsmul (p ^ v) =
          (ι' v ≫ pullback.snd Λ.f σp) ≫ ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1,
      IsIso (pullback.lift (f := (Λ.L.baseChange σp).schemeNsmul (p ^ v)) (g := ((Λ.L.baseChange σp).one (𝟙 (Spec (CommRingCat.of (ZMod p))))).1)
        (ι' v) (ι' v ≫ pullback.snd Λ.f σp) h3))
    (hι'mul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒜.baseChange (ZMod p)).Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒜.baseChange (ZMod p)).level v →+* B)) ≫ ι' v =
          ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1)

    (Rh : Type) [CommRing Rh] [Algebra Rh (ZMod p)] {h : ℕ} (𝒢 : PDivisibleGroup Rh p h) (v : ℕ)
    (φ : Spec (CommRingCat.of (ZMod p ⊗[Rh] 𝒢.level v)) ⟶ pullback Λ.f σp)
    (hφbase : φ ≫ pullback.snd Λ.f σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))))
    (hφmul : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] (x y : (𝒢.baseChange (ZMod p)).Point B v)
        (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ φ) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B)))
        (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ φ) ≫ pullback.snd Λ.f σp =
          Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))),
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : (𝒢.baseChange (ZMod p)).level v →ₐ[ZMod p] B) : (𝒢.baseChange (ZMod p)).level v →+* B)) ≫ φ =
          ((Λ.L.baseChange σp).mul (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) ⟨_, hx⟩ ⟨_, hy⟩).1) :
    ∃ ρ : (𝒜.baseChange (ZMod p)).level v →ₐc[ZMod p] (𝒢.baseChange (ZMod p)).level v,
      Spec.map (CommRingCat.ofHom (ρ : (𝒜.baseChange (ZMod p)).level v →+* (𝒢.baseChange (ZMod p)).level v)) ≫ ι' v = φ := by sorry
