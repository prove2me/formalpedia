-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_ofAlgAut_fricke_of_atkinLehnerComplement_placePin_of_representsRelSubPic_abelJacobi
-- name    : ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_fricke_of_atkinLehnerComplement_placePin_of_representsRelSubPic_abelJacobi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/1a7b2963-b610-5aa5-86f0-597be9ab803a
-- title:
--   Fricke endomorphism over A of the J_H(M) Néron object inducing w_M
-- statement:
--   Fix a prime $p$ and $M \geq 1$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and a subgroup $H \leq (\mathbb{Z}/M)^{\times}$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is trivial (`hHp`); assume $M/p \neq 0$. Assume the $q$-expansion `jqModC ℚ` of $j$ lies in the level-one $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` (`hj`), and fix a model datum $\mathfrak{X}$ of type `XHDRModelAtP p M H hpM hj` for $X_H(M)$ at $p$: it provides the two-chart integral curve over `R p` with structure morphism `toBase p (ΓM M H) hj`, the section $\mathfrak{X}.\varepsilon_{\inf}$ over `Spec (R p)`, the curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` (the $\overline{\mathbb{Q}}$-Laurent base change of the function field of $X_H(M)$) together with the isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the $\overline{\mathbb{Q}}$-fibre, and the automorphism datum $\mathfrak{X}.w$. Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, i.e. `A.LiesOverPrime p`) whose residue field is algebraically closed of characteristic $p$, an `R p`-algebra structure on $A$ with `specMap (R p) ↥A = Λ.σA` (`hσA_spec`) and with $\iota \circ (\text{structure map})$ equal to the structure map $\mathrm{R}\,p \to \overline{\mathbb{Q}}$ (`hRA`), level data $\Lambda$ (whose $\sigma_A : \operatorname{Spec} A \to$ `base p` satisfies `barPt A ≫ Λ.σA = genPt p`), and an object $O$ of type `JHNeronObjectAtP p M H hpM A hA Λ`, with underlying scheme $O.G$, structure morphism $O.g$ to `base p`, relative group law $O.L$ over `baseRing p` and bijection $O.\mathrm{pts} : J_H(M) \to$ points of $O.g$ over `genPt p`, where $J_H(M) =$ `JH M H` is the group of degree-zero divisor classes of `xHFunctionFieldBar M H`.
--
--   Write $D_0$ for the relative $\mathrm{Pic}^0$ designation $(O.G,\, O.g,\, \text{the unit point of } O.L \text{ over } \operatorname{Spec}(\mathrm{R}\,p))$ over `R p` for the curve `toBase p (ΓM M H) hj`.
--
--   The representability hypotheses are: `hD`, that $D_0$ represents, relative to the section $\mathfrak{X}.\varepsilon_{\inf}$, the subfunctor of rigidified line bundles cut out by `algEquivZeroCut` (fibrewise algebraic equivalence to zero); `hDQ`, the same for the base change of $D_0$ to $\mathbb{Q}$ relative to `sectionBaseChange ℚ 𝔛.εinf`; `hpoinc`, that the Poincaré bundle of `hDQ` is isomorphic to the $\mathbb{Q}$-base change (via `BaseChange.ofR`) of the pullback of the Poincaré bundle of `hD` along `pullback.fst O.g (specMap (R p) ℚ)`; and `hsepQ`, separatedness of the base-changed curve over $\mathbb{Q}$.
--
--   The comparison data are the morphisms $k_A$ and $k_Q$ from the $\overline{\mathbb{Q}}$-fibre `pullback (toBase …) (genPt p)` to the fibres over $A$ and over $\mathbb{Q}$, each compatible with the first projection (`hkA₁`, `hkQ₁`) and carrying the second projection to the second projection followed by `barPt A`, respectively by `specMap ℚ (AlgebraicClosure ℚ)` (`hkA₂`, `hkQ₂`).
--
--   The Abel–Jacobi data are: $\mathrm{aj}_Q$, a morphism over $\mathbb{Q}$ from the generic-fibre curve to the base of the $\mathbb{Q}$-base change of $D_0$; `hajε`, that the zero section `sectionBaseChange ℚ 𝔛.εinf` followed by $\mathrm{aj}_Q$ is the zero section of that designation; `hajcl`, that for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec} \mathbb{Q}$ and every $K$-point $x$ of the generic-fibre curve over $t$, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by $\mathrm{aj}_Q$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the point $x$ with the ideal module of the relative effective Cartier divisor of the point $t$ followed by `sectionBaseChange ℚ 𝔛.εinf` (so $\mathrm{aj}_Q$ classifies the class of $(x)-(\varepsilon)$); $\overline{\mathrm{aj}} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$, required to equal $\mathfrak{X}.\mathrm{eeta}$ followed by $k_Q$, by $\mathrm{aj}_Q$ and by `pullback.fst O.g (specMap (R p) ℚ)` (`hajbar`) and to satisfy $\overline{\mathrm{aj}} \ncong$-freely $\overline{\mathrm{aj}}$ followed by $O.g$ equal to $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by `genPt p` (`hajbar_over`); a $\overline{\mathbb{Q}}$-point $\bar{\varepsilon}$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base which corresponds to $\mathfrak{X}.\varepsilon_{\inf}$ (`hεbar`) and is sent by $\overline{\mathrm{aj}}$ to the unit point of $O.L$ (`hεbar_aj`); `hpts_law`, that $O.\mathrm{pts}$ is additive for the group law on $D_0$ obtained from `hD` through `RepresentsRelSubPic.relativeGroupLaw` for `algEquivZeroGroupCut` (this replaces the stronger requirement that $O.L$ itself be that law); and `hAJ`, that for all $\overline{\mathbb{Q}}$-points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, with $s$ corresponding to $\mathfrak{X}.\varepsilon_{\inf}$ in the sense of `hεbar`, there is a degree-zero divisor $D_v$ on `xHFunctionFieldBar M H` equal to $1 \cdot [\text{place of } x] - 1 \cdot [\text{place of } s]$ (places attached to points through $\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}$) whose class satisfies $O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of } D_v) = x$ followed by $\overline{\mathrm{aj}}$.
--
--   The cyclotomic and automorphism data are: a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ for $\{M/p\}$, with $\zeta \in L$ a primitive $(M/p)$-th root of unity (`hζ`); a ring homomorphism $\iota_A : L \to \overline{\mathbb{Q}}$ compatible with the structure maps from `R p` (`hιA`) and with $\iota_A \zeta \in A$ (`hιAζ`); an element $j'$ of `laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))`, non-zero, whose Laurent series is the image of `jqModC ℚ` under `coeffEmb L` (`hj'`); an $L$-algebra automorphism $\sigma$ of that field, non-zero on $j'$, which on the image of `qExpFunctionFieldC ℚ (ΓM p (H.map (ZMod.unitsMap hpM)))` acts by the $q$-expansion substitution `qExpand ℚ (M / p)` (`hσ`); a $\overline{\mathbb{Q}}$-algebra automorphism $\theta_Q$ of `xHFunctionFieldBar M H` which is the $\overline{\mathbb{Q}}$-shadow of $\sigma$ along `coeffMap ιA` (`hθσ`); a $\overline{\mathbb{Q}}$-algebra automorphism $\theta_p$ of `xHFunctionFieldBar M H` whose associated semilinear automorphism describes the action of $\mathfrak{X}.w$ on places, in the sense that whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base satisfy $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.w.\mathrm{hom}$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, then the place of $y'$ is `SemilinearAut.ofAlgAut θp` applied to the place of $y$ (`hwgen_p`); and a $\overline{\mathbb{Q}}$-algebra automorphism $w_M$ of `xHFunctionFieldBar M H` whose action on $J_H(M)$ equals the composite action of $\theta_p$ after $\theta_Q$ (`hw`).
--
--   Under these hypotheses there exists a morphism $W$ of $G_A := O.G \times_{\mathrm{base}\,p, \Lambda.\sigma_A} \operatorname{Spec} A$ to itself over its structure morphism `RelativeGroupLaw.baseChangeStr Λ.σA O.g` to $\operatorname{Spec} A$, such that both of the following hold.
--
--   First, $W$ is a homomorphism for the base-changed group law: for every scheme $T$, every $s : T \to \operatorname{Spec} A$ and every pair of $T$-points $x, y$ of $G_A$ over $s$, the product $(O.L.\mathrm{baseChange}\ \Lambda.\sigma_A).\mathrm{mul}\ s\ x\ y$ followed by $W$ equals the product of ($x$ followed by $W$) and ($y$ followed by $W$).
--
--   Second, $W$ induces the action of $w_M$ on $\overline{\mathbb{Q}}$-points: for every $x \in J_H(M)$, $O.\mathrm{pts}(\mathrm{SemilinearAut.ofAlgAut}\ w_M \cdot x)$ equals the point over `genPt p` obtained, via `genOfBaseChangePt Λ.hσA`, from the composite of $W$ with the point of $G_A$ over `barPt A` that corresponds by the pullback property (`RelativeGroupLaw.baseChangePointOfBase Λ.σA`) to $O.\mathrm{pts}\ x$ read over `barPt A ≫ Λ.σA` through `castOver Λ.hσA.symm`.
--
--   The morphism $W$ is the Fricke involution $w_M$ of $X_H(M)$ realised as an endomorphism, over the valuation ring $A$, of the relative group object attached to $\mathrm{Pic}^0$ of the integral model at $p$, obtained from the Atkin–Lehner datum at $p$ together with the complementary Atkin–Lehner automorphism coming from the $q$-expansion substitution $q \mapsto q^{M/p}$. It is used by the statements on idempotents, pairings and the counting of toric characters for $J_H(M)$ at $p$, where an $A$-endomorphism realising $w_M$ on $\overline{\mathbb{Q}}$-points is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_ofAlgAut_fricke_of_atkinLehnerComplement_placePin_of_representsRelSubPic_abelJacobi.lean

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
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_fricke_of_atkinLehnerComplement_placePin_of_representsRelSubPic_abelJacobi
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    [Algebra (R p) ↥A] (hσA_spec : specMap (R p) ↥A = Λ.σA)
    (kA : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hkA₁ : kA ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkA₂ : kA ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ barPt A)
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsepQ : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})

    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))

    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)

    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))

    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)

    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (hAJ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    [NeZero (M / p)]
    (hRA : ∀ r : R p, ((algebraMap (R p) ↥A r : ↥A) : AlgebraicClosure ℚ) = algebraMap (R p) (AlgebraicClosure ℚ) r)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {M / p} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ (M / p))
    (ιA : L →+* AlgebraicClosure ℚ)
    (hιA : ∀ r : R p, ιA (algebraMap (R p) L r) = algebraMap (R p) (AlgebraicClosure ℚ) r)
    (hιAζ : ιA ζ ∈ A)
    (j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))
    (hj' : ((j' : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) = coeffEmb L (jqModC ℚ)) [Fact (j' ≠ 0)]
    (σ : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))) ≃ₐ[L] ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H))))
    (hσ : ∀ (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) (u : ↥(qExpFunctionFieldC ℚ (ΓM p (H.map (ZMod.unitsMap hpM))))),
        (f : LaurentSeries L) = coeffEmb L (u : LaurentSeries ℚ) →
          ((σ f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L) = coeffEmb L (qExpand ℚ (M / p) (u : LaurentSeries ℚ)))
    [Fact (σ j' ≠ 0)]
    (θQ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθσ : ∀ (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) (g : ↥(xHFunctionFieldBar M H)),
        (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap ιA (f : LaurentSeries L) →
          ((θQ g : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffMap ιA ((σ f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (ΓM M H)))) : LaurentSeries L))

    (θp : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen_p : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θp • 𝔛.Meta.pointEquivPlace y)

    (wM : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hw : ∀ x : JH M H, SemilinearAut.ofAlgAut wM • x = SemilinearAut.ofAlgAut θp • (SemilinearAut.ofAlgAut θQ • x)) :
    ∃ W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
          (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
          (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W)) ∧
      (∀ x : JH M H, O.pts (SemilinearAut.ofAlgAut wM • x) =
        genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W)) := by sorry
