-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
-- name    : ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a60e50b1-0d02-54b0-9571-afa043357c2f
-- title:
--   Configured representative of a p-torsion class with Néron section
-- statement:
--   Setting. Fix a prime $p$, a level $M \neq 0$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ satisfying `hHp`: every unit of $\mathbb{Z}/M$ whose image under the reduction `ZMod.unitsMap` associated with $(M/p) \mid M$ equals $1$ lies in $H$. Fix a valuation subring $Pl$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `Pl.LiesOverPrime p`, i.e. $p$ is a non-unit of $Pl$, and assume its residue field $\kappa =$ `IsLocalRing.ResidueField ↥Pl` has characteristic $p$ and is algebraically closed. Assume `hj`, that the $q$-expansion $j$-series `jqModC ℚ` belongs to `qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))`. Fix a model $\mathfrak{X}$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) for the curve `X p (ΓM M H) hj` over `Spec (R p)`, with its associated curve model $\mathfrak{X}.\mathrm{Meta}$ of the function field `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ and the isomorphism $\mathfrak{X}.\mathtt{eeta}$ of $\mathfrak{X}.\mathrm{Meta}.C$ with the base change of `toBase p (ΓM M H) hj` to $\overline{\mathbb{Q}}$; fix level data $\Lambda$ of type [`ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl`](def/ModularCurve_JHNeronObjectAtP.html#L32) and an object $O$ of type [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), so that $O$ provides a scheme $O.G$ over `base p` with structure morphism $O.g$, a relative group law $O.L$, and a bijection $O.\mathrm{pts}$ from `JH M H` $=$ `Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)` onto the sections of $O.g$ over `genPt p`, together with its smoothness, separatedness, surjectivity, Hecke and $n$-torsion data.
--
--   Configuration hypotheses. Writing $\mathcal{D}$ for the designation $\langle O.G, O.g, (O.L.\mathrm{one}\,(\mathbb{1}))_1, (O.L.\mathrm{one}\,(\mathbb{1}))_2\rangle$ of type `RelativePic0Designation (R p) (toBase p (ΓM M H) hj)`, built from $O.G$ with the unit section of the relative group law as zero section, the statement assumes the following groups of hypotheses, whose content is summarised here.
--
--   (i) Representability: `hD` asserts that $\mathcal{D}$ represents the relative sub-Picard functor of `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ and cut out by `algEquivZeroCut` (fibrewise algebraic equivalence to zero); `hDQ` asserts the corresponding statement for the base change of the curve to $\mathbb{Q}$, the section `sectionBaseChange ℚ 𝔛.εinf` and the base-changed designation $\mathcal{D}_{\mathbb{Q}}$. `hsep` asserts that the base change of the curve to $\mathbb{Q}$ is separated.
--
--   (ii) Abel–Jacobi datum over $\mathbb{Q}$: $\mathrm{ajQ}$ is a morphism from the base-changed curve to $\mathcal{D}_{\mathbb{Q}}.\mathrm{toBase}$ over $\mathbb{Q}$; `hajQε` says that it carries the section `sectionBaseChange ℚ 𝔛.εinf` to the zero section of $\mathcal{D}_{\mathbb{Q}}$; `hajQ` says that for every field $K$, every $K$-point $t$ of $\mathbb{Q}$ and every section $x$ of the base-changed curve over $t$, the pullback along $x$ followed by $\mathrm{ajQ}$ of the Poincaré bundle of `hDQ` is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor `RelEffCartierDiv.ofPoint` attached to $x$ with the ideal module of the divisor attached to $t$ followed by the $\varepsilon_{\inf}$-section; `hpoinc` asserts that the Poincaré bundle of `hDQ` is isomorphic to the bundle obtained from the Poincaré bundle of `hD` by pullback along the first projection of $O.g$ against `specMap (R p) ℚ` and the base-change functor `BaseChange.ofR` to $\mathbb{Q}$.
--
--   (iii) Comparison of fibres: $\mathrm{kQ}$ is a morphism from the pullback of the curve along `genPt p` to its pullback along `specMap (R p) ℚ`, and `hkQ₁`, `hkQ₂` say that it commutes with the first projections and intertwines the second projections through `specMap ℚ (AlgebraicClosure ℚ)`.
--
--   (iv) Geometric Abel–Jacobi map: $\overline{\mathrm{aj}} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$ and a point $\overline{\varepsilon}$ of $\mathfrak{X}.\mathrm{Meta}.C$ over $\overline{\mathbb{Q}}$ (a section of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$). The hypothesis `hajbar` identifies $\overline{\mathrm{aj}}$ with $\mathfrak{X}.\mathtt{eeta}$ followed by $\mathrm{kQ}$, by $\mathrm{ajQ}$ and by the first projection of $O.g$ against `specMap (R p) ℚ`; `hajbar_over` says that $\overline{\mathrm{aj}}$ followed by $O.g$ equals $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by `genPt p`; `hεbar` says that $\overline{\varepsilon}$, transported through $\mathfrak{X}.\mathtt{eeta}$ and the first projection, is `genPt p` followed by $\mathfrak{X}.\varepsilon_{\inf}$; and `hεbar_aj` says that $\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ is `genPt p` followed by the unit section of $O.L$.
--
--   (v) Compatibility of $O.\mathrm{pts}$: `hpts_law` says that $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD` through `RepresentsRelSubPic.relativeGroupLaw` for the group cut `algEquivZeroGroupCut`; `hAJ` says that for all points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ over $\overline{\mathbb{Q}}$ with $s$ lying over the $\varepsilon_{\inf}$-section in the sense of `hεbar`, there is a degree-zero divisor $D_v$ of `xHFunctionFieldBar M H` with $D_v = [\,\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}\,x\,] - [\,\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}\,s\,]$ whose class satisfies $(O.\mathrm{pts}\,[D_v])_1 = x$ followed by $\overline{\mathrm{aj}}$.
--
--   (vi) The place: a ring homomorphism $\rho :$ `R p` $\to Pl$ with `hρ`, that $\rho$ followed by the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$ is the structure map of `R p`, and `hσA`, that $\Lambda.\sigma_A =$ `Spec.map (CommRingCat.ofHom ρ)`.
--
--   Data. Let $z \in$ `JH M H` be such that `ExtendsToPlace Pl Λ.σA (O.pts z)` holds, i.e. there is a section of $O.g$ over $\Lambda.\sigma_A$ whose composition with `barPt Pl` is $(O.\mathrm{pts}\,z)_1$, and such that $p \cdot z = 0$. Let $D'$ be a degree-zero divisor of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ with class $z$, let $f \neq 0$ be an element of `xHFunctionFieldBar M H` with $p\,D'(v) = \mathrm{ord}_v f$ for every place $v$ (`hdiv`), let $y$ be a Laurent series over $Pl$ whose image under `coeffMap Pl.subtype` is the Laurent series $f$ (`hfy`) and whose image under `coeffMap (IsLocalRing.residue ↥Pl)` is non-zero (`hy`), and let $g \in$ `Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` have Laurent series equal to that reduction of $y$ (`hg`).
--
--   Conclusion. There exist an element $h$ of `xHFunctionFieldBar M H`, Laurent series $x_h, y_h$ over $Pl$, an element $\bar h$ of `Fbar p M H hpM κ`, a natural number $k$, functions $c : \mathrm{Fin}\,k \to \mathrm{Fin}\,2$, $y_{(\cdot)} : \mathrm{Fin}\,k \to$ (points of $\mathfrak{X}.\mathrm{Meta}.C$ over $\overline{\mathbb{Q}}$, i.e. sections of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$), $u : \mathrm{Fin}\,k \to$ (morphisms from `Spec Pl` to `X p (ΓM M H) hj` over `Spec.map (CommRingCat.ofHom ρ)`), $u_\kappa : \mathrm{Fin}\,k \to$ (morphisms from `Spec κ` to the fibre `fibre ((IsLocalRing.residue ↥Pl).comp ρ)`), $P : \mathrm{Fin}\,k \to$ `closedPoints (𝔛.Mfib Pl hPl ρ hρ).C`, $n : \mathrm{Fin}\,k \to \mathbb{Z}$, and a degree-zero divisor $D_v$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, such that all of the following hold:
--
--   1. $h \neq 0$;
--
--   2. the reduction `coeffMap (IsLocalRing.residue ↥Pl) xh` is non-zero;
--
--   3. the reduction `coeffMap (IsLocalRing.residue ↥Pl) yh` is non-zero;
--
--   4. the Laurent series of $h$ over $\overline{\mathbb{Q}}$ times the image of $y_h$ under `coeffMap Pl.subtype` equals the image of $x_h$ under `coeffMap Pl.subtype`;
--
--   5. the Laurent series of $\bar h$ over $\kappa$ times the reduction of $y_h$ equals the reduction of $x_h$;
--
--   6. for every $i$, `barPt Pl` followed by $u_i$ equals $y_i$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection;
--
--   7. for every $i$, the range of the underlying map of $u_i$ is contained in $\mathfrak{X}.\mathrm{smoothLocus}$ as a set of points of `X p (ΓM M H) hj`;
--
--   8. for every $i$, $u_{\kappa,i}$ followed by the first projection equals `Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl))` followed by $u_i$;
--
--   9. for every $i$, $u_{\kappa,i}$ followed by the second projection is the identity;
--
--   10. for every $i$, the underlying map of $\mathfrak{X}.\mathtt{efib}\ Pl\ hPl\ \rho\ h\rho$ followed by $\mathfrak{X}.\mathrm{comp}\ Pl\ hPl\ \rho\ h\rho\ (c\,i)$ sends $P_i$ to the image of the closed point of $\kappa$ under $u_{\kappa,i}$;
--
--   11. $\sum_{i : c(i) = 0} n_i = 0$;
--
--   12. $\sum_{i : c(i) = 1} n_i = 0$;
--
--   13. $D_v = \sum_i n_i\,[\,\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}\,y_i\,]$ as a finitely supported function on places;
--
--   14. $D_v(v) = D'(v) + \mathrm{ord}_v h$ for every place $v$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$;
--
--   15. for every place $v$ of `Fbar p M H hpM κ` over $\kappa$,
--   $$\mathrm{ord}_v\bigl(g\,\bar h^{\,p}\bigr) = p \cdot \Bigl(\sum_{i : c(i) = 0} n_i\,[\,(\mathfrak{X}.\mathrm{Mfib}\ Pl\ hPl\ \rho\ h\rho).\mathrm{placeOfPoint}\,(P_i)\,]\Bigr)(v).$$
--
--   This is the normalisation step in the analysis of a $p$-torsion class of $J_H(M)$ whose Néron point extends over a place above $p$: the class is replaced by a representative supported at points of the model lying in the smooth locus, with component-by-component degree zero, and the function exhibiting $p$-divisibility is adjusted by a factor that is a unit for the valuation attached to the $q$-expansion embedding, so that after reduction the divisor of $g\bar h^{\,p}$ is exactly $p$ times an explicit divisor on the component indexed by $0$. It is used by [`ModularCurve.JHNeronObjectAtP.exists_configured_rep_pic0Mk_eq_toPic0Pair_mk_of_mem_finPts_of_forall_dvd_ord_tauFree`](thm.html#ModularCurve.JHNeronObjectAtP.exists_configured_rep_pic0Mk_eq_toPic0Pair_mk_of_mem_finPts_of_forall_dvd_ord_tauFree) and by [`ModularCurve.JHNeronObjectAtP.mem_finPts_iff_forall_ssPlacesQExp_dvd_ord_of_rootFunction_smul_of_coe_eq_coeffMap_residue_of_abelJacobiPin_of_algEquiv`](thm.html#ModularCurve.JHNeronObjectAtP.mem_finPts_iff_forall_ssPlacesQExp_dvd_ord_of_rootFunction_smul_of_coe_eq_coeffMap_residue_of_abelJacobiPin_of_algEquiv), which compute the special-fibre coordinates of finite $p$-torsion classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_configured_rep_ord_mul_pow_eq_of_extendsToPlace_pts_of_smul_eq_zero
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
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (z : ModularCurve.JH M H)
    (hz : ExtendsToPlace Pl Λ.σA (O.pts z))
    (hpz : p • z = 0)
    (D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hD' : AlgebraicCurve.Pic0.mk D' = z)
    (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (hdiv : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (p : ℤ) * (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v = v.ord f)
    (y : LaurentSeries ↥Pl)
    (hfy : (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y)
    (hy : ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0)
    (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
    (hg : (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y) :
    ∃ (h : ↥(ModularCurve.xHFunctionFieldBar M H)) (xh yh : LaurentSeries ↥Pl) (hbar : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))
        (k : ℕ) (c : Fin k → Fin 2)
        (yv : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : Fin k → NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (uκ : Fin k → (Spec (CommRingCat.of (IsLocalRing.ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ)))
        (P : Fin k → closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
        (n : Fin k → ℤ)
        (Dv : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))),

        h ≠ 0 ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ≠ 0 ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh ≠ 0 ∧
        (h : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype yh = ModularCurve.coeffMap Pl.subtype xh ∧
        (hbar : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) yh =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) xh ∧

        (∀ i, ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ (u i).1 = (yv i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ∧
        (∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
        (∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ (u i).1) ∧
        (∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _) ∧
        (∀ i, (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥Pl))) ∧
        (∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0) ∧
        (∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0) ∧
        ((Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) =
          ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (yv i)) 1) ∧

        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (Dv : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v =
            (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v + v.ord h) ∧

        ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
          v.ord (g * hbar ^ p) =
            (p : ℤ) * (∑ i ∈ Finset.univ.filter (fun i => c i = 0),
              n i • Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint (P i)) 1) v := by sorry
