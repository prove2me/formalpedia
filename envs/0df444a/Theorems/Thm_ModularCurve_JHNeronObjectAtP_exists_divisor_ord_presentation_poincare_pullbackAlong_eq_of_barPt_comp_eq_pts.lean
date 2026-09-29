-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
-- name    : ModularCurve.JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a599b6fe-cdb3-5140-a73b-3836dd490f30
-- title:
--   Generic divisor of a presentation of σ^*Poincaré on the Pl-model
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$ (`hpM`, `hpM2`), a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial (`hHp`), and a valuation subring $\mathrm{Pl}$ of $\overline{\mathbb{Q}}$ with `Pl.LiesOverPrime p`, i.e. $p$ lies in the non-units of $\mathrm{Pl}$ (`hPl`), whose residue field is of characteristic $p$ and algebraically closed. Fix also the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the intermediate field `qExpFunctionFieldC ℚ ⊤`, a Deligne–Rapoport-type integral model $\mathfrak{X}$ of `XHDRModelAtP p M H hpM hj` at $p$ (which carries in particular a section `𝔛.εinf` of `toBase p (ΓM M H) hj` over $R_p$, a curve model `𝔛.Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`, and an isomorphism `𝔛.eeta` of `𝔛.Meta.C` with the pullback of the model along $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec} R_p$), a level datum $\Lambda$ and a Néron object $O$ of `JHNeronObjectAtP p M H hpM Pl hPl Λ`, with total space `O.G`, structure morphism `O.g` to `base p`, relative group law `O.L` and bijection `O.pts` from `JH M H` to the $\overline{\mathbb{Q}}$-points of `O.g` over `genPt p`.
--
--   Throughout, $\mathcal{D}$ denotes the relative $\mathrm{Pic}^0$ designation $\langle O.G,\ O.g,\ (O.L.one\ (\mathbf{1}))_1\rangle$ over $R_p$, whose zero section is the identity section of the group law.
--
--   Representability hypotheses. `hD` asserts that $\mathcal{D}$ represents the relative sub-Picard functor of `toBase p (ΓM M H) hj` rigidified along `𝔛.εinf` for the condition `algEquivZeroCut`, whose predicate on a rigidified line bundle is `FibrewiseAlgEquivZero`: it provides a rigidified line bundle `hD.poincare` satisfying that predicate, the universal property that any rigidified line bundle satisfying it is the pullback of `hD.poincare` along a unique morphism to `O.G` over the base, and triviality of the pullback along the zero section. `hDQ` asserts the same for the base change to $\mathbb{Q}$, namely for `baseChange (R p) (toBase p (ΓM M H) hj) ℚ` with section `sectionBaseChange ℚ 𝔛.εinf` and designation $\mathcal{D}$ base changed to $\mathbb{Q}$; `hsep` asserts that this generic fibre is separated; `hpoinc` provides an isomorphism between the line bundle of `hDQ.poincare` and that of the descent-to-$\mathbb{Q}$ `BaseChange.ofR` of the pullback of `hD.poincare` along the first projection of `pullback O.g (specMap (R p) ℚ)`.
--
--   Abel–Jacobi hypotheses. `ajQ` is a morphism from the generic fibre over $\mathbb{Q}$ to the total space of the base-changed designation, over the base; `hajQε` says that it carries `sectionBaseChange ℚ 𝔛.εinf` to the zero section; `hajQ` says that for every field $K$, every morphism $t : \operatorname{Spec} K \to \operatorname{Spec} \mathbb{Q}$ and every $K$-point $x$ of the generic fibre over $t$, the line bundle of the pullback of `hDQ.poincare` along $x$ followed by `ajQ` is isomorphic to the tensor product of `RelEffCartierDiv.lineBundle` of the point divisor `RelEffCartierDiv.ofPoint` at $x$ with `RelEffCartierDiv.idealModule` of the point divisor at $t$ followed by the section, i.e. to $\mathcal{O}(x - \varepsilon)$. Further, `kQ` is a morphism from `pullback (toBase p (ΓM M H) hj) (genPt p)` to `pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ)` commuting with the first projections (`hkQ₁`) and intertwining the second projections through $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$ (`hkQ₂`); `ajbar : 𝔛.Meta.C ⟶ O.G` is required by `hajbar` to be `𝔛.eeta` followed by `kQ`, then `ajQ` and then the first projection of `pullback O.g (specMap (R p) ℚ)`, and by `hajbar_over` to satisfy $ajbar$ followed by `O.g` $=$ `𝔛.Meta.toBase` followed by `genPt p`. The $\overline{\mathbb{Q}}$-point `εbar` of `𝔛.Meta.C` (a section of `𝔛.Meta.toBase`) is required to lie over `𝔛.εinf` (`hεbar`) and to be sent by $ajbar$ to the identity section of the group law (`hεbar_aj`). The hypothesis `hpts_law` requires `O.pts` to be additive for the relative group law `RepresentsRelSubPic.relativeGroupLaw` furnished by `hD` with respect to `algEquivZeroGroupCut`, and `hAJ` requires that for all $\overline{\mathbb{Q}}$-points $x, s$ of `𝔛.Meta.C` with $s$ lying over `𝔛.εinf` as in `hεbar` there is a degree-zero divisor $Dv$ on $(\overline{\mathbb{Q}}, \mathrm{xHFunctionFieldBar}\ M\ H)$ whose underlying divisor is $\mathrm{single}(\mathrm{place}(x)) - \mathrm{single}(\mathrm{place}(s))$ under `𝔛.Meta.pointEquivPlace`, with $(O.\mathrm{pts}(\mathrm{Pic0.mk}\ Dv))_1 = x$ followed by $ajbar$.
--
--   The $\mathrm{Pl}$-model. A ring homomorphism $\rho : R_p \to \mathrm{Pl}$ is given with `hρ`: $\rho$ followed by the inclusion of $\mathrm{Pl}$ into $\overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$. Write $\mathfrak{X}_{\mathrm{Pl}}$ for `pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))`, assumed integral (`hint`). A morphism $g_A$ from `𝔛.Meta.C` to $\mathfrak{X}_{\mathrm{Pl}}$ is given whose composite with the first projection equals that of `𝔛.eeta` (`hgA₁`) and whose composite with the second projection is `𝔛.Meta.toBase` followed by `barPt Pl` (`hgA₂`).
--
--   The class and the section. An element $z$ of `JH M H` is given together with a degree-zero divisor $D'$ on $(\overline{\mathbb{Q}}, \mathrm{xHFunctionFieldBar}\ M\ H)$ with `Pic0.mk D' = z` (`hD'`), and a morphism $\sigma : \operatorname{Spec}\mathrm{Pl} \to O.G$ over `Spec.map (CommRingCat.ofHom ρ)` with respect to `O.g`, such that `barPt Pl` followed by $\sigma$ equals $(O.\mathrm{pts}\ z)_1$ (`hσ`).
--
--   The presentation. Set $\mathcal{L} = (hD.poincare.pullbackAlong\ \sigma).L$, an invertible module on $\mathfrak{X}_{\mathrm{Pl}}$. A family of additive maps $\varphi_U : \Gamma(\mathcal{L}, U) \to K(\mathfrak{X}_{\mathrm{Pl}})$, indexed by the opens $U$ of $\mathfrak{X}_{\mathrm{Pl}}$, is given, compatible with restriction to nonempty opens (`hφnat`), semilinear over the structure sheaf in the sense $\varphi_U(a \cdot m) = \mathrm{alg}(a)\,\varphi_U(m)$ (`hφsmul`), and injective on nonempty opens (`hφinj`).
--
--   The identification of function fields. A ring isomorphism $e$ from $K(\mathfrak{X}_{\mathrm{Pl}})$ to `xHFunctionFieldBar M H` is given which is compatible with germs along $g_A$ (`he`): for every open $U$ with $g_A^{-1}U$ nonempty and every $a \in \Gamma(\mathfrak{X}_{\mathrm{Pl}}, U)$, $e$ of the germ of $a$ in the function field equals `𝔛.Meta.ffEquiv.symm` of the germ in $K(\mathrm{Meta}.C)$ of the image of $a$ under $g_A$ on $g_A^{-1}U$.
--
--   Conclusion. There exist a divisor $D_\varphi$ on $(\overline{\mathbb{Q}}, \mathrm{xHFunctionFieldBar}\ M\ H)$ and an element $g_1$ of `xHFunctionFieldBar M H` such that:
--
--   (i) $g_1 \neq 0$;
--
--   (ii) for every place $v$ of $\mathrm{xHFunctionFieldBar}\ M\ H$ over $\overline{\mathbb{Q}}$, $D_\varphi(v) = D'(v) + v.\mathrm{ord}(g_1)$, where $D'$ is read as a divisor and $v.\mathrm{ord}$ is minus the logarithm of the adic valuation at $v$;
--
--   (iii) for every open $U$ of $\mathfrak{X}_{\mathrm{Pl}}$, every $\overline{\mathbb{Q}}$-point $q$ of `𝔛.Meta.C` (a section of `𝔛.Meta.toBase`) whose image under $g_A$ of the closed point of $\operatorname{Spec}\overline{\mathbb{Q}}$ lies in $U$, and every $m \in \Gamma(\mathcal{L}, U)$, both of the following hold, with $v_q =$ `𝔛.Meta.pointEquivPlace q` the place attached to $q$:
--
--   (iii.a) if $\varphi_U(m) \neq 0$ then $-D_\varphi(v_q) \le v_q.\mathrm{ord}(e(\varphi_U(m)))$;
--
--   (iii.b) if $m$ generates $\mathcal{L}$ near $g_A(q)$, in the sense that for every open $W \le U$ containing the image point and every $m' \in \Gamma(\mathcal{L}, W)$ there is $a \in \Gamma(\mathfrak{X}_{\mathrm{Pl}}, W)$ with $m' = a \cdot (m|_W)$, then $v_q.\mathrm{ord}(e(\varphi_U(m))) = -D_\varphi(v_q)$.
--
--   This is the step that reads the divisor of a function-field presentation of the pullback along a $\mathrm{Pl}$-valued Néron section of the Poincaré bundle of $J_H(M)$: on the geometric generic fibre that divisor is $D'$ up to the principal divisor of a single nonzero function, with exact order of vanishing at points where the chosen section generates the invertible module. It is used by [`ModularCurve.JHNeronObjectAtP.dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue`](thm.html#ModularCurve.JHNeronObjectAtP.dvd_ord_of_iterate_mul_eq_one_of_barPt_comp_eq_pts_of_coe_eq_coeffMap_residue) and by [`ModularCurve.JHNeronObjectAtP.exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero`](thm.html#ModularCurve.JHNeronObjectAtP.exists_configured_rep_and_isUnit_mul_pow_of_extendsToPlace_pts_of_smul_eq_zero) in the analysis of the component group and of the horizontal behaviour of divisor classes at a place above $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 800000 in
open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.exists_divisor_ord_presentation_poincare_pullbackAlong_eq_of_barPt_comp_eq_pts
    (p : ℕ)
    [Fact p.Prime]
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
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
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    [hint : IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]

    (z : ModularCurve.JH M H)
    (D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hD' : AlgebraicCurve.Pic0.mk D' = z)
    (σ : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g)
    (hσ : ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ σ.1 = (O.pts z).1)

    (φ : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Γ((hD.poincare.pullbackAlong σ).L, U) →+ ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField : Type))
    (hφnat : ∀ (U V : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((hD.poincare.pullbackAlong σ).L, U), φ V ((hD.poincare.pullbackAlong σ).L.presheaf.map (homOfLE h).op m) = φ U m)
    (hφsmul : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) [Nonempty U] (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)) (m : Γ((hD.poincare.pullbackAlong σ).L, U)),
      φ U (a • m) = algebraMap Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U) (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField a * φ U m)
    (hφinj : ∀ U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens, Nonempty U → Function.Injective (φ U))

    (e : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).functionField ≃+* ↥(ModularCurve.xHFunctionFieldBar M H))
    (he : ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hne : Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ U))) (a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), U)),
      haveI : Nonempty (Scheme.Opens.toScheme U) := by
        obtain ⟨⟨x, hx⟩⟩ := hne
        exact ⟨⟨gA.base x, hx⟩⟩
      e ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).germToFunctionField U a) =
        𝔛.Meta.ffEquiv.symm (𝔛.Meta.C.germToFunctionField (gA ⁻¹ᵁ U) ((gA.app U).hom a))) :
    ∃ (Dφ : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
      (g₁ : ↥(ModularCurve.xHFunctionFieldBar M H)), g₁ ≠ 0 ∧

      (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        Dφ v = (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord g₁) ∧

      ∀ (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (q : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (hq : gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ U) (m : Γ((hD.poincare.pullbackAlong σ).L, U)),
        haveI : Nonempty (Scheme.Opens.toScheme U) := ⟨⟨_, hq⟩⟩
        (φ U m ≠ 0 → -Dφ (𝔛.Meta.pointEquivPlace q) ≤ (𝔛.Meta.pointEquivPlace q).ord (e (φ U m))) ∧
        ((∀ (W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens) (hW : W ≤ U), gA.base (q.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ W →
            ∀ m' : Γ((hD.poincare.pullbackAlong σ).L, W), ∃ a : Γ((pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))), W), m' = a • (hD.poincare.pullbackAlong σ).L.presheaf.map (homOfLE hW).op m) →
          (𝔛.Meta.pointEquivPlace q).ord (e (φ U m)) = -Dφ (𝔛.Meta.pointEquivPlace q)) := by sorry
