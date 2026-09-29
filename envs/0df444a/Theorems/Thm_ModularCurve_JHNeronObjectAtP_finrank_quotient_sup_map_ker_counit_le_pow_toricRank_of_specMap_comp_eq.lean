-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq
-- name    : ModularCurve.JHNeronObjectAtP.finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/62e85a7a-01af-5c9a-89db-5ce22a8dfc94
-- title:
--   A bound p^{vt} for the joint kernel on finite levels
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ in which $p$ is a non-unit and whose residue field is algebraically closed of characteristic $p$; let $\Lambda$ be level data at $p$ (a scheme $\Lambda.X$ with structure morphism $\Lambda.f$ to $\operatorname{Spec}$ of the ring of rationals with denominator coprime to $p$, a relative group law $\Lambda.L$, and parametrisations of its generic and residual points), assumed with $\Lambda.f$ proper, and let $O$ be a Néron object for $J_H(M)$ over $\Lambda$, with structure morphism $O.g$, group law $O.L$ and recorded toric rank $O.\mathrm{toricRank}$. Assume given: a commutative ring $R_h$ with a map to $\mathbb{Z}/p$, a ring map $\rho_h$ from the base ring to $R_h$, and a $p$-divisible group $\mathcal{G}$ over $R_h$ of height $h$ whose levels come with morphisms $\iota_v : \operatorname{Spec}\mathcal{G}_v \to O.G$ lying over $\rho_h$, which are closed immersions into the base change of $O.G$ along $\rho_h$ and are killed by $p^v$ (that is, $\iota_v$ followed by multiplication by $p^v$ factors through the unit section); a point $\sigma_p : \operatorname{Spec}(\mathbb{Z}/p) \to$ the base, through which $R_h \to \mathbb{Z}/p$ and $\rho_h$ factor; morphisms $\iota^p_v : \operatorname{Spec}(\mathbb{Z}/p \otimes_{R_h} \mathcal{G}_v) \to$ the fibre of $O.g$ over $\sigma_p$, specified by their two projections; a pair $q_0, q_1$ of morphisms from the $\sigma_p$-fibre of $O.g$ to that of $\Lambda.f$ over $\operatorname{Spec}(\mathbb{Z}/p)$ which are additive on points and whose base change along $\mathbb{Z}/p \to$ the residue field of $Pl$ (this factorisation being part of the data) recovers the pair $O.\mathrm{abqFibre}$; and a $p$-divisible group $\mathcal{A}$ over the base ring of height $h_\Lambda$, with $\sigma_p$ the spectrum of an algebra map from that base ring to $\mathbb{Z}/p$, together with morphisms $\iota'_v$ from $\operatorname{Spec}$ of the level $v$ of $\mathcal{A} \otimes \mathbb{Z}/p$ to the $\sigma_p$-fibre of $\Lambda.f$, which are sections of the structure map, closed immersions, additive on points, and identify that level with the kernel of multiplication by $p^v$ (the canonical map to the pullback of the $p^v$-multiplication along the unit section being an isomorphism). The conclusion is that for every $v$ and every pair $\varphi_0, \varphi_1$ of $\mathbb{Z}/p$-algebra maps from the level $v$ of $\mathcal{A} \otimes \mathbb{Z}/p$ to $\mathbb{Z}/p \otimes_{R_h} \mathcal{G}_v$ such that $\operatorname{Spec}\varphi_i$ followed by $\iota'_v$ equals $\iota^p_v$ followed by $q_i$, one has $$\dim_{\mathbb{Z}/p}\bigl((\mathbb{Z}/p \otimes_{R_h} \mathcal{G}_v)/(\varphi_0(I) + \varphi_1(I))\bigr) \le p^{\,v \cdot O.\mathrm{toricRank}},$$ where $I$ denotes the kernel of the counit (the augmentation ideal) of the level $v$ of $\mathcal{A} \otimes \mathbb{Z}/p$, and $\varphi_i(I)$ the ideal it generates.
--
--   The quotient in question is the affine algebra of the scheme-theoretic locus in the finite level $\mathcal{G}_v \otimes \mathbb{F}_p$ on which both maps to the abelian quotient vanish, so the assertion bounds the degree of this joint kernel by $p^{vt}$ with $t$ the toric rank. It rests on the identification of the toric part of the special fibre with the joint kernel of the pair $O.\mathrm{abqFibre}$ as a split torus, together with the computation of the degree of $\mu_{p^v}^t$, and it feeds the surjectivity and dimension count in [`ModularCurve.surjective_productMap_and_finrank_eq_levelTorsion_raynaudQuotient_baseChange_of_finPtsWitness`](thm.html#ModularCurve.surjective_productMap_and_finrank_eq_levelTorsion_raynaudQuotient_baseChange_of_finPtsWitness).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq.lean

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

theorem ModularCurve.JHNeronObjectAtP.finrank_quotient_sup_map_ker_counit_le_pow_toricRank_of_specMap_comp_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hΛf : IsProper Λ.f)

    (Rh : Type) [CommRing Rh] [Algebra Rh (ZMod p)]
    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)

    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ ModularCurve.JZeroNeronObjectAtP.base p)
    (hσp : Spec.map (CommRingCat.ofHom (algebraMap Rh (ZMod p))) ≫ Spec.map (CommRingCat.ofHom ρh) = σp)
    (ιp : ∀ v : ℕ, Spec (CommRingCat.of (ZMod p ⊗[Rh] 𝒢.level v)) ⟶ pullback O.g σp)
    (hιp₁ : ∀ v : ℕ, ιp v ≫ pullback.fst O.g σp =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : 𝒢.level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ ι v)
    (hιp₂ : ∀ v : ℕ, ιp v ≫ pullback.snd O.g σp = Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v))))
    (q : Fin 2 → NeronModelInfra.SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f))

    [Algebra (ZMod p) (ResidueField ↥Pl)]
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl))) ≫ σp = ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA)
    (hqmul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : NeronModelInfra.SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i)))
    (hqbc : ∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (ModularCurve.JZeroNeronObjectAtP.resPt Pl ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥Pl)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1)

    {hΛ : ℕ} (𝒜 : PDivisibleGroup (ModularCurve.JZeroNeronObjectAtP.baseRing p) p hΛ)
    [Algebra (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p)]
    (hσp' : σp = Spec.map (CommRingCat.ofHom (algebraMap (ModularCurve.JZeroNeronObjectAtP.baseRing p) (ZMod p))))
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
    :
    ∀ (v : ℕ) (φ : Fin 2 → ((𝒜.baseChange (ZMod p)).level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v)),
      (∀ i : Fin 2, Spec.map (CommRingCat.ofHom (φ i : (𝒜.baseChange (ZMod p)).level v →+* ZMod p ⊗[Rh] 𝒢.level v)) ≫ ι' v = ιp v ≫ (q i).1) →
      Module.finrank (ZMod p) ((ZMod p ⊗[Rh] 𝒢.level v) ⧸
        (Ideal.map (φ 0) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v))) ⊔
          Ideal.map (φ 1) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) ((𝒜.baseChange (ZMod p)).level v))))) ≤
        p ^ (v * O.toricRank) := by sorry
