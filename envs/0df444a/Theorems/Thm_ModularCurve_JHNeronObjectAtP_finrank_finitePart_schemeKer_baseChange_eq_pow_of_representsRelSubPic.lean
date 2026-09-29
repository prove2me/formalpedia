-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_finrank_finitePart_schemeKer_baseChange_eq_pow_of_representsRelSubPic
-- name    : ModularCurve.JHNeronObjectAtP.finrank_finitePart_schemeKer_baseChange_eq_pow_of_representsRelSubPic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/5bce529b-2ca9-5086-91ba-7cdeb319606d
-- title:
--   Rank of the finite part of p^v-torsion of J_H(M)
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit in $Pl$, whose residue field is algebraically closed of characteristic $p$. Assume the $q$-expansion of $j$ lies in the level-$\mathrm{SL}(2,\mathbb{Z})$ $q$-expansion function field over $\mathbb{Q}$, and fix integral model data $\mathfrak{X}$ of type `XHDRModelAtP`, level data $\Lambda$ and an object $O$ of `JHNeronObjectAtP` over $Pl$. Two representability hypotheses are assumed: the designation $(O.G, O.g)$ with its unit section represents the rigidified relative Picard functor of `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$, cut out by the condition that the line bundle be algebraically equivalent to zero on all geometric fibres, and likewise $(\Lambda.X, \Lambda.f)$ represents the corresponding functor for `toBase p (XHDRLevel.ΓN p M H hpM) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$. Let $R_h$ be a henselian local domain with a faithful algebra structure over which $\overline{\mathbb{Q}}$ is an algebra, such that every element of $R_h$ maps into $Pl$, and such that the maximal ideal of $R_h$ consists exactly of the elements whose image has $Pl$-valuation $<1$; let $\rho_h \colon R(p) \to R_h$ be a ring map compatible with the two embeddings into $\overline{\mathbb{Q}}$, where $R(p)$ is the subring of rationals with denominator coprime to $p$. Finally let $v \in \mathbb{N}$, let $A$ be a finite free $R_h$-algebra, and let $j \colon \operatorname{Spec} A \to$ the kernel scheme of $[p^v]$ for the base change of the relative group law $O.L$ along $\operatorname{Spec}(\rho_h)$ be a morphism which is simultaneously an open and a closed immersion, which is compatible with the structure morphisms to $\operatorname{Spec} R_h$, and whose image on points contains every point of that kernel scheme lying over the closed point of $R_h$. Then $\operatorname{rank}_{R_h} A = p^{\,v\,(t + 4g')}$, where $t$ is the natural number `O.toricRank` recorded in $O$ and $g'$ is `genusFF` — the dimension over the residue field of $Pl$ of the first cohomology $H^1(0)$ — of the $q$-expansion function field over that residue field at level [`CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)`](def/CohCarrier_Level.html#L133).
--
--   This computes the order of the finite part of the $p^v$-torsion of the Néron identity component of $J_H(M)$ at a prime of multiplicative-by-good (semistable) reduction: a split torus of rank $t$ extended by two copies of the Jacobian of the smooth level $M/p$ curve, whose $p^v$-torsion contributes $p^{2vg'}$ each. It is the rank input for the construction of the $p$-divisible group attached to the Néron object, used in [`ModularCurve.exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic`](thm.html#ModularCurve.exists_pDivisibleGroup_closedImmersion_finitePart_jHNeronObjectAtP_of_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_finrank_finitePart_schemeKer_baseChange_eq_pow_of_representsRelSubPic.lean

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
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve

theorem ModularCurve.JHNeronObjectAtP.finrank_finitePart_schemeKer_baseChange_eq_pow_of_representsRelSubPic
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (v : ℕ) (A : Type) [CommRing A] [Algebra Rh A] [Module.Finite Rh A] [Module.Free Rh A]
    (j : Spec (CommRingCat.of A) ⟶ (O.L.baseChange (Spec.map (CommRingCat.ofHom ρh))).schemeKer (p ^ v))
    (hjstr : j ≫ (O.L.baseChange (Spec.map (CommRingCat.ofHom ρh))).schemeKerStr (p ^ v) =
      Spec.map (CommRingCat.ofHom (algebraMap Rh A)))
    (hjo : IsOpenImmersion j) (hjc : IsClosedImmersion j)
    (hcov : ∀ x : ↥((O.L.baseChange (Spec.map (CommRingCat.ofHom ρh))).schemeKer (p ^ v)),
      ((O.L.baseChange (Spec.map (CommRingCat.ofHom ρh))).schemeKerStr (p ^ v)).base x = IsLocalRing.closedPoint Rh →
        x ∈ Set.range j.base) :
    Module.finrank Rh A = p ^ (v * (O.toricRank + 4 * AlgebraicCurve.genusFF (ResidueField ↥Pl) ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))) := by sorry
