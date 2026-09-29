-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_span_inertia_sub_of_mem_toricLattice_tateModule_jH_of_abelJacobiPin_of_atkinLehner
-- name    : ModularCurve.JHNeronObjectAtP.exists_pow_smul_mem_span_inertia_sub_of_mem_toricLattice_tateModule_jH_of_abelJacobiPin_of_atkinLehner
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/51045a9e-8edf-5ebf-8f10-6857ace6e60b
-- title:
--   Toric Tate vectors as inertia coboundaries up to bounded ℓ-power
-- statement:
--   Fix a prime $p$ and $M \ne 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$, and the hypothesis $hj$ that the Laurent series `jqModC` over $\mathbb{Q}$ lies in the $q$-expansion function field `qExpFunctionFieldC` of $SL(2,\mathbb{Z})$; let $\mathfrak{X}$ be an integral model datum `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the base ring $R\,p$, with its curve model `Meta` of the geometric function field $\bar{F}_H =$ `xHFunctionFieldBar M H`. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $\bar{F}_H$ which, on functions coming from level $M/p$ with subgroup `infSubgroup p M H hpM`, acts on Laurent series by $q \mapsto q^p$ (`qExpand` at $p$), and assume the Atkin–Lehner compatibility `hwgen`: whenever two $\overline{\mathbb{Q}}$-points of `Meta.C` correspond under $\mathfrak{X}.w$, their places are exchanged by the semilinear automorphism `SemilinearAut.ofAlgAut` $\theta$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits and algebraically closed residue field of characteristic $p$, and let $(\Lambda, O)$ be level data and a Néron object for $J_H(M)$ at $A$. A block of hypotheses, summarised here, pins $O$ down as a relative $\mathrm{Pic}^0$: $O.G$ with its zero section represents the functor of rigidified line bundles satisfying the fibrewise algebraically-trivial condition `algEquivZeroCut`, both over $R\,p$ and after base change to $\mathbb{Q}$ (with separatedness, Poincaré-bundle compatibilities, and the pullback formula for the line bundle attached to a point), $O.\mathrm{pts}$ is additive for the resulting relative group law, and an Abel–Jacobi morphism $\overline{aj}$ is fixed so that for geometric points $x$ and $s$ of `Meta.C`, $s$ lying over the chosen base point, the class of the degree-zero divisor $[x] - [s]$ is sent by $O.\mathrm{pts}$ to $x$ followed by $\overline{aj}$. Finally let $\ell \ne p$ be a prime and let $T^t$ be a $\mathbb{Z}_\ell$-submodule of the Tate module $T =$ [`TateModule ℓ (JH M H)`](def/EllipticCurve_TateModule.html#L15) (compatible systems $(x_n)$ with $\ell^n x_n = 0$, $\ell x_{n+1} = x_n$, in $\mathrm{Pic}^0(\bar{F}_H)$) consisting exactly of those $x$ with $\mathrm{proj}_n(x) \in O.\mathrm{toricPts}(\ell^n)$ for all $n$. The conclusion: there is $k \in \mathbb{N}$ such that $\ell^k \cdot x$ lies in the $\mathbb{Z}_\ell$-span of $\{\sigma w - w : \sigma \in$ `A.inertiaSubgroupIn ℚ`$,\ w \in T\}$ for every $x \in T^t$, the action being the coordinatewise Galois action [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174).
--
--   This is the Tate-module form of the non-degeneracy of Grothendieck's monodromy pairing for the semistable abelian variety $J_H(M)$ at $p \parallel M$: the toric lattice is contained in the image of $\sigma - 1$ for inertia at $p$, up to a bounded power of $\ell$ measuring the $\ell$-part of the component group. It feeds the level-lowering step [`ModularCurve.JH.exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd`](thm.html#ModularCurve.JH.exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd), where inertia-invariance of a Tate-module vector is converted into a statement about the old part at level $M/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_pow_smul_mem_span_inertia_sub_of_mem_toricLattice_tateModule_jH_of_abelJacobiPin_of_atkinLehner.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_WeilDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_pow_smul_mem_span_inertia_sub_of_mem_toricLattice_tateModule_jH_of_abelJacobiPin_of_atkinLehner
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (Tt : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n)) :
    ∃ k : ℕ, ∀ x ∈ Tt, (((ℓ : ℕ) : ℤ_[ℓ]) ^ k) • x ∈
      Submodule.span ℤ_[ℓ] {m : TateModule ℓ (JH M H) | ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∃ w : TateModule ℓ (JH M H), m = TateModule.rep ℓ (JH M H) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ w - w} := by sorry
