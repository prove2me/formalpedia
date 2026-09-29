-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag
-- name    : ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/09adf573-c105-5226-8a14-ecd1b3919b30
-- title:
--   Good inertia-invariant classes of J_H(M) extend over A
-- statement:
--   Fix a prime $p$ and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a divisibility $p \mid M$ (`hpM`) together with $p^2 \nmid M$ (`hpM2`), so that $p$ exactly divides $M$; `hHp` requires that every unit of $(\mathbb{Z}/M)^\times$ whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$ lies in $H$, i.e. $H$ contains the kernel of reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, and $M/p \neq 0$. The hypothesis `hj` states that the $q$-series `jqModC ℚ` lies in the field `qExpFunctionFieldC ℚ ⊤` of $q$-expansions at full level over $\mathbb{Q}$, and $\mathfrak{X}$ is a model datum `XHDRModelAtP p M H hpM hj`: an integral model `toBase p (ΓM M H) hj` of the modular curve of level $\Gamma_M(H)$ over $R_p$, proper, flat, integral, normal and of finite presentation, together with a smooth proper model at level $\Gamma_N(p,M,H)$, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`, the isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the geometric generic fibre, the cusp section $\mathfrak{X}.\varepsilon_{\infty}$, and the special-fibre data $\mathfrak{X}.\mathrm{Mfib}$, $\mathfrak{X}.\mathrm{efib}$, $\mathfrak{X}.\mathrm{comp}$.
--
--   Further, $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, that is $p$ is a non-unit of $A$, whose residue field is of characteristic $p$ and algebraically closed; $\Lambda$ is a `JHNeronObjectAtP.LevelData p M H hpM A`, supplying in particular a morphism $\Lambda.\sigma_A : \operatorname{Spec} A \to \operatorname{Spec}(\mathrm{baseRing}\,p)$ with `barPt A` followed by $\Lambda.\sigma_A$ equal to `genPt p`; and $O$ is a `JHNeronObjectAtP p M H hpM A hA Λ`, in particular a smooth separated group object $O.G \to \operatorname{Spec}(\mathrm{baseRing}\,p)$ with structure morphism $O.g$, relative group law $O.L$, a bijection $O.\mathrm{pts} : J_H(M) \simeq \{$sections of $O.g$ over `genPt p`$\}$, and a finite set $O.\mathrm{ssFinset}$ of pairs of places of the special-fibre function field.
--
--   The representability and Abel–Jacobi group of hypotheses is formulated for the relative $\mathrm{Pic}^0$ designation $D$ whose total space is $O.G$, whose structure morphism is $O.g$, and whose zero section is the unit point $O.L.\mathrm{one}$ at the identity of $\operatorname{Spec}(R_p)$. Here `hD` asserts that $D$ represents the relative sub-Picard functor cut out by `algEquivZeroCut` (rigidified line bundles whose geometric fibres are algebraically equivalent to zero) for `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_\infty$, and `hDQ` asserts the corresponding representability over $\mathbb{Q}$ for the base-changed curve, the base-changed cusp section and $D$ base changed to $\mathbb{Q}$; `hsep` states that the generic fibre `baseChange (R p) (toBase p (ΓM M H) hj) ℚ` is separated. The morphism $\mathrm{ajQ}$ is a section over the generic fibre of the structure morphism of $D \otimes \mathbb{Q}$, $\mathrm{kQ}$ compares the pullback along `genPt p` with the pullback along `specMap (R p) ℚ`, $\overline{\mathrm{aj}} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$ is a morphism, and $\overline{\varepsilon}$ is a $\overline{\mathbb{Q}}$-point of $\mathfrak{X}.\mathrm{Meta}.C$ over the base. These are constrained as follows: `hpoinc` gives an isomorphism between the Poincaré bundle of `hDQ` and the descent to the base change of the pullback of the Poincaré bundle of `hD` along the first projection of $O.g$; `hajQε` says that the base-changed cusp section followed by $\mathrm{ajQ}$ is the zero section of $D \otimes \mathbb{Q}$; `hajQ` is the Abel–Jacobi property of $\mathrm{ajQ}$: for every field $K$, every $K$-point $t$ of $\operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the generic fibre, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by $\mathrm{ajQ}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the relative effective Cartier divisor of the cusp point $t$ followed by the base-changed $\varepsilon_\infty$; `hkQ₁` and `hkQ₂` state that $\mathrm{kQ}$ is compatible with the first projections and, on second projections, with `specMap ℚ (AlgebraicClosure ℚ)`; `hajbar` defines $\overline{\mathrm{aj}}$ as $\mathfrak{X}.\mathrm{eeta}$ followed by $\mathrm{kQ}$, by $\mathrm{ajQ}$ and by the first projection of $O.g$ along `specMap (R p) ℚ`; `hajbar_over` says that $\overline{\mathrm{aj}}$ followed by $O.g$ equals $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by `genPt p`; `hεbar` says that $\overline{\varepsilon}$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection equals `genPt p` followed by $\mathfrak{X}.\varepsilon_\infty$; `hεbar_aj` says that $\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ is `genPt p` followed by the unit point; `hpts_law` says that $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD` via the group cut `algEquivZeroGroupCut`; and `hAJ` says that for all $\overline{\mathbb{Q}}$-points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, with $s$ satisfying the cusp condition of `hεbar`, there is a degree-zero divisor $D_v$ on `xHFunctionFieldBar M H` equal to $\mathrm{single}(\mathrm{pointEquivPlace}\,x) - \mathrm{single}(\mathrm{pointEquivPlace}\,s)$ whose class satisfies $(O.\mathrm{pts}(\mathrm{Pic}^0.\mathrm{mk}\,D_v))_1 = x$ followed by $\overline{\mathrm{aj}}$.
--
--   The place-specialization group of hypotheses consists of: an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H`; an $\overline{\mathbb{Q}}$-algebra map $\alpha$ from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to `xHFunctionFieldBar M H`, with $\alpha$ integral (`hα`), $\theta \circ \alpha$ integral (`hβ`), and $\alpha$ acting as the identity on the underlying Laurent series (`hα_coe`); a ring homomorphism $\rho : R_p \to A$ with `hρ` asserting that $\rho$ followed by the inclusion of $A$ is the structure map $R_p \to \overline{\mathbb{Q}}$, and `hσA` identifying $\Lambda.\sigma_A$ with $\operatorname{Spec}\rho$; a unit $\mathrm{pb}$ of $\mathbb{Z}/(M/p)$ reducing to $p$ (`hpb`); a self-map $\delta$ of the places of `Fbar p M H hpM (ResidueField A)` which by `hδ` is the action of the semilinear automorphism attached to the mod-$p$ diamond automorphism `diamondActionModL` at the $\Gamma_0(M/p)$-lift of $\mathrm{pb}$; a place specialization $\mathrm{Psp}$ and a prolongation datum $\mathrm{Rpd}$ for $\mathrm{Psp}$ and $\theta$; the type dichotomy `hTD` for $(\alpha, \theta\circ\alpha, \delta)$, stating that for every place $W$ of `xHFunctionFieldBar M H` either $\mathrm{reduceFst}\,W$ is the mod-$p$ Frobenius pullback of $\mathrm{reduceSnd}\,W$ or $\delta$ applied to the Frobenius pullback of $\mathrm{reduceFst}\,W$ equals $\mathrm{reduceSnd}\,W$; the model law `hmodel`, the conjunction of the two divisor laws and the two cusp laws of $\mathrm{Rpd}$; and the order law at fixed places `hO`.
--
--   Finally, two compatibility hypotheses relate $\mathfrak{X}$'s special fibre to the reductions. Both are indexed by a component $i \in \mathrm{Fin}\,2$, a $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, a point $u$ of the model over $\operatorname{Spec}\rho$ whose reduction along `barPt A` agrees with $y$ transported by $\mathfrak{X}.\mathrm{eeta}$, a residue-field point $u_\kappa$ of the fibre of the model at $\rho$ composed with the residue map, subject to the two projection identities, and a closed point $P_0$ of $\mathfrak{X}.\mathrm{Mfib}$ lying, after $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map, over the image of the closed point under $u_\kappa$. Under these data `hcompat` asserts that the place of $P_0$ is $\mathrm{Psp}.\mathrm{reduceFst}\,\alpha$ applied to the place of $y$ when $i = 0$, and $\mathrm{Psp}.\mathrm{reduceSnd}\,(\theta\circ\alpha)\,\delta$ applied to the place of $y$ otherwise, while `hcompat'` asserts the crossed identities: for $i = 0$, $\mathrm{reduceSnd}$ of the place of $y$ equals $\delta$ of the mod-$p$ Frobenius pullback of the place of $P_0$, and otherwise $\mathrm{reduceFst}$ of the place of $y$ equals the mod-$p$ Frobenius pullback of the place of $P_0$.
--
--   The conclusion: for every $x$ in `JHPlaceSpecialization.inertiaInvariants M H A`, that is every class in $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathrm{xHFunctionFieldBar}\,M\,H)$ fixed by every element of the inertia subgroup of $A$ over $\mathbb{Q}$, if $x$ is a good class for the datum $(\mathrm{Psp}, \alpha, \theta\circ\alpha, \delta, O.\mathrm{ssFinset})$ — i.e. there exists a degree-zero divisor $D$ on `xHFunctionFieldBar M H` with $\mathrm{Psp}.\mathrm{IsGoodDiv}$ holding for $D$, with $\mathrm{Psp}.\mathrm{glueData}$ of $D$ lying in the admissible subgroup of gluing data for $O.\mathrm{ssFinset}$ (both components of degree zero and vanishing at the two coordinates of each prescribed pair), and with $\mathrm{Pic}^0.\mathrm{mk}\,D = x$ — then `ExtendsToPlace A Λ.σA (O.pts x)` holds: there is a section $s$ of $O.g$ over $\Lambda.\sigma_A$ such that the underlying morphism of $O.\mathrm{pts}\,x$ equals `barPt A` followed by $s$. In other words, the $\overline{\mathbb{Q}}$-point of $O.G$ attached to $x$ extends to an $A$-valued point.
--
--   This is the 'good implies extends' half of the specialisation bridge for the Jacobian of the modular curve of level $\Gamma_H(M)$ at a prime $p$ exactly dividing $M$: a class invariant under the inertia group of the chosen valuation subring $A$ and good for the place-specialization kit is shown to extend to a section over $\operatorname{Spec} A$ of the group object supplied by the Néron object datum. It feeds the counting bound [`ModularCurve.JHNeronObjectAtP.exists_forall_natCard_torsion_inf_inertiaInvariants_le_natCard_finPts_mul_of_abelJacobiPin_of_wgen`](thm.html#ModularCurve.JHNeronObjectAtP.exists_forall_natCard_torsion_inf_inertiaInvariants_le_natCard_finPts_mul_of_abelJacobiPin_of_wgen), where the extendable classes are identified with the finite part in the level-lowering argument at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag.lean

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
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_isGoodClass_of_abelJacobiPin_offDiag
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    ∀ x : ↥(JHPlaceSpecialization.inertiaInvariants M H A),
      Psp.IsGoodClass α (θ.toAlgHom.comp α) hα hβ δ O.ssFinset (x : JH M H) → ExtendsToPlace A Λ.σA (O.pts (x : JH M H)) := by sorry
