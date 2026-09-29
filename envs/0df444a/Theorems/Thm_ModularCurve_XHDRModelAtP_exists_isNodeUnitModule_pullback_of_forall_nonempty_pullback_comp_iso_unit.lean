-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isNodeUnitModule_pullback_of_forall_nonempty_pullback_comp_iso_unit
-- name    : ModularCurve.XHDRModelAtP.exists_isNodeUnitModule_pullback_of_forall_nonempty_pullback_comp_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/33fc41a0-9b12-5ebd-bc8a-fdeb28f0b2ff
-- title:
--   Component-wise trivial invertible module is a node-unit module
-- statement:
--   Fix natural numbers $p$ (prime) and $M \ne 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and hypotheses $p \mid M$, $p^2 \nmid M$, together with the assumption that every unit of $(\mathbb{Z}/M)^\times$ whose image under reduction along $(M/p) \mid M$ is $1$ lies in $H$; assume $j$-series $\mathtt{jqModC}\ \mathbb{Q}$ lies in the $q$-expansion function field of the full modular group, and let $\mathfrak{X}$ be a datum of type `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map; $\kappa$ is an $R\,p$-algebra via the residue map composed with $\rho$. The assertion is: for every morphism $\beta$ from $\operatorname{Spec}\kappa$ to $\operatorname{Spec}A$ over $\operatorname{Spec}(R\,p)$ whose underlying morphism is $\mathtt{resPt}\,A$; assuming (i) the two projections of the fibre product of the two component morphisms $\mathfrak{X}.\mathtt{comp}\,0$, $\mathfrak{X}.\mathtt{comp}\,1$ (each going from the base change to $\kappa$ of the $\Gamma_N(p,M,H)$-curve into the base change to $\kappa$ of the $\Gamma_M(M,H)$-curve) agree after composition with the structure map to $\operatorname{Spec}\kappa$, so that the index set $\iota$ of sections of that fibre product over $\operatorname{Spec}\kappa$ is defined; (ii) $\iota$ is finite; (iii) the map sending such a section $j$ to the image of the closed point under $j$ followed by the first projection is injective; (iv) whenever two points $q_1,q_2$ of the base-changed $\Gamma_N$-curve have the same image under the respective component morphisms, they arise as the images of the closed point under some $j \in \iota$ followed by the first, respectively second, projection; and (v) $L$ is an invertible module on the base change to $\operatorname{Spec}A$ of the $\Gamma_M$-curve (invertible in the sense that every point has a neighbourhood on which the restriction of $L$ is isomorphic to the unit sheaf) whose pullback along each component morphism followed by $\mathtt{baseChangeSnd}\ \beta$ is isomorphic to the monoidal unit on the special fibre — there exists a family $u$ of units of $\Gamma(\operatorname{Spec}\kappa,\top)$ indexed by $\iota$ such that the pullback of $L$ to the $\kappa$-fibre (along the first projection followed by $\mathtt{baseChangeSnd}\ \beta$) satisfies `IsNodeUnitModule` for the ambient base-changed $\Gamma_M$-curve, the two component morphisms, the node sections $j \mapsto j$ followed by the first and second projection respectively, the identity of $\operatorname{Spec}\kappa$ and the units $u$: that is, it admits maps to the pushforwards of the unit sheaves of the two components which, on every open set, identify its sections with exactly those pairs of functions on the two components satisfying, at every crossing $j$, the relation that the first function equals $u_j$ times the second.
--
--   This is the bridge, for the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ with $p \parallel M$, between an invertible module on the model whose restriction to each of the two components of the special fibre is trivial and a description of its restriction to the special fibre as two trivial bundles glued by a tuple of units at the crossings, in the spirit of the Picard-functor computations for curves with nodal special fibre. It is obtained from the general statement [`AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit`](thm.html#AlgebraicGeometry.TwoGluedCurves.exists_isNodeUnitModule_of_pullback_curveChange_iso_unit) about two glued curves over an algebraically closed field, and feeds the construction of points of the Néron model attached to inertia at $p$ in [`ModularCurve.JHNeronObjectAtP`](def/ModularCurve_JHNeronObjectAtP.html#L53).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_isNodeUnitModule_pullback_of_forall_nonempty_pullback_comp_iso_unit.lean

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
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.TwoGluedCurves
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_isNodeUnitModule_pullback_of_forall_nonempty_pullback_comp_iso_unit
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (β : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (Spec.map (CommRingCat.ofHom ρ)))
      (_ : β.1 = resPt A)

      (hc : pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)) =
        pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)))

      [Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))))]
      (_ : Function.Injective fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) =>
        (j.1 ≫ pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (_ : ∀ (q₁ q₂ : ↥(pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) (ResidueField ↥A)))),
        (𝔛.comp A hA ρ hρ 0).base q₁ = (𝔛.comp A hA ρ hρ 1).base q₂ →
        ∃ j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))), q₁ = (j.1 ≫ pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          q₂ = (j.1 ≫ pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base (IsLocalRing.closedPoint (ResidueField ↥A)))

      (L : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules) (_ : Scheme.Modules.IsInvertible L)
      (_ : ∀ i : Fin 2, Nonempty ((Scheme.Modules.pullback (𝔛.comp A hA ρ hρ i ≫ baseChangeSnd (toBase p (ΓM M H) hj) β)).obj L ≅
        𝟙_ (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).Modules)),
      ∃ u : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) → Γ(Spec (CommRingCat.of (ResidueField ↥A)), ⊤)ˣ,
        IsNodeUnitModule (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (⟨(𝔛.comp A hA ρ hρ 0), 𝔛.comp_over A hA ρ hρ 0⟩ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)) (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A))) (⟨(𝔛.comp A hA ρ hρ 1), 𝔛.comp_over A hA ρ hρ 1⟩ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A)) (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)))
          (fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) =>
            (⟨j.1 ≫ pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1), by rw [Category.assoc]; exact j.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))))
          (fun j : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))) =>
            (⟨j.1 ≫ pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1), by rw [Category.assoc, hc]; exact j.2⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (baseChange (R p) (toBase p (ΓN p M H hpM) hj) (ResidueField ↥A))))
          (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) u
          ((Scheme.Modules.pullback (pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) ≫
            baseChangeSnd (toBase p (ΓM M H) hj) β)).obj L) := by sorry
