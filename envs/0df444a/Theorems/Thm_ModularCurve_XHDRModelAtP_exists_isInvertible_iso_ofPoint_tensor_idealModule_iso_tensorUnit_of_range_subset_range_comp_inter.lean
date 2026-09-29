-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter
-- name    : ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/49aab583-d232-5f80-9d5b-704efbdbc965
-- title:
--   Inertia line bundle 𝒪(σ V-V) at a crossing
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit whose image in $(\mathbb Z/(M/p))^\times$ is $1$, with $M/p$ nonzero, and the hypothesis `hj` placing `jqModC ℚ` in the $q$-expansion function field of level $\mathrm{SL}(2,\mathbb Z)$; let $\mathfrak X$ be a model datum `XHDRModelAtP p M H hpM hj`, whose morphism `toBase p (ΓM M H) hj` to $\operatorname{Spec} (R\,p)$ is proper. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ and with algebraically closed residue field of characteristic $p$, and let $\rho : R\,p \to A$ be a ring map compatible with $R\,p \to \overline{\mathbb Q}$; $\psi$ and $\beta$ are the morphisms over the base given by the inclusion $A \hookrightarrow \overline{\mathbb Q}$ and by the residue map $A \to \kappa_A$ respectively. Let $V$ be a place of the geometric function field $\overline{\mathbb Q}\cdot F(\Gamma_H(M))$, let $s$ be an $A$-point of the model whose base change along $A \hookrightarrow \overline{\mathbb Q}$ is the geometric point attached to $V$ through `𝔛.Meta.pointEquivPlace` and the isomorphism `𝔛.eeta`, and let $y$ be a section over $\operatorname{Spec}\kappa_A$ of the special fibre at level $\Gamma_M$ whose first projection is the reduction of $s$. Assume the image of $y$ lies in the image of both components `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1`, and let $\sigma$ be an automorphism of $\overline{\mathbb Q}$ over $\mathbb Q$ lying in the inertia subgroup at $A$. Let $\bar y_1, \bar y_2$ be the geometric points of the model attached to the places $\sigma \cdot V$ (via `arithmeticGalois`) and $V$. Then there exists a sheaf of modules $L$ on the base change of the model to $A$ such that: $L$ is invertible, i.e. every point has an open neighbourhood on which $L$ restricts to the unit module; the pullback of $L$ along `baseChangeSnd` of $\psi$ is isomorphic to the tensor product of the dual ideal module of the degree-one relative effective Cartier divisor `RelEffCartierDiv.ofPoint` at $\bar y_1$ with the ideal module of the one at $\bar y_2$; and for each $i \in \{0,1\}$ the pullback of $L$ along `𝔛.comp A hA ρ hρ i` followed by `baseChangeSnd` of $\beta$ is isomorphic to the unit module on the fibre at level $\Gamma_N$ over $\kappa_A$.
--
--   This is the construction, on the Deligne–Rapoport model of $X_H(M)$ base changed to a valuation ring $A$ above $p$, of an invertible sheaf whose geometric generic fibre is $\mathcal O(\sigma V - V)$ for $\sigma$ in the inertia group at $A$ and $V$ a place reducing to a crossing of the two components of the special fibre, and which is trivial on each of the two components. It feeds the analysis of the inertia action on divisor classes supported at crossings, and is used in [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter) and in the corresponding statement about the Néron object of $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ))) (hψ : ψ.1 = barPt A)
    (β : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (Spec.map (CommRingCat.ofHom ρ)))
    (hβ : β.1 = resPt A)

    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
      ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫
        pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    (y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hy₁ : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
    (hy₂ : y ≫ pullback.snd _ _ = 𝟙 _)

    (hc : (Set.range y.base ⊆ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
        Set.range y.base ⊆ Set.range (𝔛.comp A hA ρ hρ 1).base))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)

    (ybar₁ ybar₂ : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj))
    (hybar₁ : ybar₁.1 = ((𝔛.Meta.pointEquivPlace).symm
      (arithmeticGalois (L := (AlgebraicClosure ℚ)) (xHFunctionField M H) σ • V)).1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hybar₂ : ybar₂.1 = ((𝔛.Meta.pointEquivPlace).symm V).1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p)) :
    ∃ L : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules,
      Scheme.Modules.IsInvertible L ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase p (ΓM M H) hj) ψ)).obj L ≅
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₁.1 ybar₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₂.1 ybar₂.2).idealModule) ∧
      (∀ i : Fin 2, Nonempty ((Scheme.Modules.pullback (𝔛.comp A hA ρ hρ i ≫ baseChangeSnd (toBase p (ΓM M H) hj) β)).obj L ≅
        𝟙_ (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).Modules)) := by sorry
