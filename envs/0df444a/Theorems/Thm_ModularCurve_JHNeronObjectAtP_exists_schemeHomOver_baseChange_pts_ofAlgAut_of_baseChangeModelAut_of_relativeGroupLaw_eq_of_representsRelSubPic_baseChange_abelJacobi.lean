-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_ofAlgAut_of_baseChangeModelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_baseChange_abelJacobi
-- name    : ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_of_baseChangeModelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_baseChange_abelJacobi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/17ad49c9-253d-5e3b-8e2f-d56f198b82ae
-- title:
--   Model automorphism over A induces an endomorphism of G_A
-- statement:
--   Fix a prime $p$ and a non-zero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ such that every unit of $\mathbb{Z}/M$ whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial belongs to $H$ (`hHp`). Assume `hj`: the Laurent series `jqModC ℚ` lies in the $q$-expansion function field of the full modular group over $\mathbb{Q}$, so that the two-chart integral model `toBase p (ΓM M H) hj` of $X_H(M)$ over the ring `R p` is available, and fix $\mathfrak{X}$ : `XHDRModelAtP p M H hpM hj`, a Deligne–Rapoport-style arithmetic model structure on that morphism; it records properness, flatness, integrality and local finite presentation of `toBase p (ΓM M H) hj`, integral closedness of the sections over affine opens, properness and smoothness of relative dimension $1$ of the model at level `ΓN p M H hpM`, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`, an isomorphism $\mathfrak{X}.\mathrm{eeta}$ from $\mathfrak{X}.\mathrm{Meta}.C$ onto the $\overline{\mathbb{Q}}$-base change of the model compatible with the structural morphisms, Galois equivariance of the induced bijection between $\overline{\mathbb{Q}}$-points and places, a pinning of the finite chart against $q$-expansions, smoothness and geometric integrality of the generic fibre, and further clauses (summarised here); $\mathfrak{X}.\varepsilon_{\inf}$ denotes the distinguished section of `toBase p (ΓM M H) hj` over the identity of $\operatorname{Spec}(\mathtt{R}\,p)$.
--
--   Fix further a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`), whose residue field is algebraically closed of characteristic $p$; level data $\Lambda$ : `JHNeronObjectAtP.LevelData p M H hpM A`, consisting of a morphism $\sigma_A : \operatorname{Spec} A \to \mathrm{base}\,p$ with $\mathrm{barPt}\,A \mathbin{\text{followed by}} \sigma_A = \mathrm{genPt}\,p$, a scheme over $\mathrm{base}\,p$ with a relative group law, and dictionaries for the generic and special fibres; and $O$ : `JHNeronObjectAtP p M H hpM A hA Λ`, whose data include a scheme $O.G$ with structural morphism $O.g : O.G \to \mathrm{base}\,p$, a relative group law $O.L$ on $O.g$, a bijection $O.\mathrm{pts}$ from $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \mathtt{xHFunctionFieldBar } M\ H)$ onto the points of $O.g$ over $\mathrm{genPt}\,p$, commutativity of $O.L$, smoothness, separatedness, local finiteness of type, quasi-compactness and surjectivity of $O.g$, preconnectedness of its fibres, additivity and Galois equivariance of $O.\mathrm{pts}$, Hecke morphisms with their compatibilities, and flatness and surjectivity of multiplication by $n$ (summarised here).
--
--   Write $D$ for the relative $\mathrm{Pic}^0$ designation over `R p` with total space $O.G$, structural morphism $O.g$ and zero section the underlying morphism of the unit point $O.L.\mathrm{one}$ at the identity of $\operatorname{Spec}(\mathtt{R}\,p)$.
--
--   The representability hypotheses are as follows. `hD` asserts that $D$ represents the rigidified relative Picard functor of `toBase p (ΓM M H) hj` along $\mathfrak{X}.\varepsilon_{\inf}$ cut out by `algEquivZeroCut`, i.e. by the condition that a rigidified line bundle be, after pullback to each geometric fibre over an algebraically closed field, algebraically equivalent to zero; the representability datum consists of a Poincaré rigidified bundle satisfying that condition, the universal property that every such bundle over a base $t$ is the pullback of the Poincaré bundle along a unique point over $t$, and triviality of the pullback along the zero section. `hL` asserts that $O.L$ is the relative group law transported from `hD` through the group-theoretic cut `algEquivZeroGroupCut`. With $A$ an `R p`-algebra, `hσA_spec` identifies `specMap (R p) ↥A` with $\Lambda.\sigma_A$; `hDA` asserts that the base change of $D$ to $A$ represents, in the same sense, the rigidified relative Picard functor of the $A$-base change of the model along the base-changed section; `hpoincA` supplies an isomorphism between the Poincaré bundle of `hDA` and the base change to $A$ of the pullback of the Poincaré bundle of `hD` along the first projection of $O.g$ and `specMap (R p) ↥A`; `hLA` asserts that for every scheme $T$ over $\operatorname{Spec} A$ the multiplication of the group law transported from `hDA` agrees with the multiplication of the base change along `specMap (R p) ↥A` of the group law transported from `hD`. Analogously over $\mathbb{Q}$: `hDQ` is the corresponding representability statement for the $\mathbb{Q}$-base change of the model, `hpoinc` the corresponding comparison of Poincaré bundles, and `hsepQ` asserts that the $\mathbb{Q}$-base change `baseChange (R p) (toBase p (ΓM M H) hj) ℚ` is separated.
--
--   The comparison morphisms are $k_A$ from the fibre product of `toBase p (ΓM M H) hj` with $\mathrm{genPt}\,p$ to its fibre product with `specMap (R p) ↥A`, compatible with the first projections (`hkA₁`) and, via $\mathrm{barPt}\,A$, with the second projections (`hkA₂`), and $k_Q$ into the fibre product with `specMap (R p) ℚ`, compatible with the first projections (`hkQ₁`) and, via `specMap ℚ (AlgebraicClosure ℚ)`, with the second projections (`hkQ₂`).
--
--   The Abel–Jacobi data consist of: a point $\mathrm{aj}_Q$ of the base-changed designation over the $\mathbb{Q}$-fibre of the model; `hajε`, which states that the base-changed cuspidal section followed by $\mathrm{aj}_Q$ is the zero section of the base-changed designation; `hajcl`, which states that for every field $K$, every morphism $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every point $x$ of the $\mathbb{Q}$-fibre over $t$, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by $\mathrm{aj}_Q$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the point $x$ with the ideal module of the relative effective Cartier divisor of the point $t$ followed by the base-changed cuspidal section; a morphism $\overline{\mathrm{aj}} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$ with `hajbar` identifying it with $\mathfrak{X}.\mathrm{eeta}$ followed by $k_Q$, by $\mathrm{aj}_Q$ and by the first projection of $O.g$ along `specMap (R p) ℚ`, and `hajbar_over` asserting that $\overline{\mathrm{aj}}$ followed by $O.g$ equals $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by $\mathrm{genPt}\,p$; a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, pinned to the cusp by `hεbar` ($\overline{\varepsilon}$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection equals $\mathrm{genPt}\,p$ followed by $\mathfrak{X}.\varepsilon_{\inf}$) and satisfying `hεbar_aj` ($\overline{\varepsilon}$ followed by $\overline{\mathrm{aj}}$ equals $\mathrm{genPt}\,p$ followed by the unit point of $O.L$); `hpts_law`, the additivity of $O.\mathrm{pts}$ for the group law transported from `hD`; and `hAJ`, which asserts that for all $\overline{\mathbb{Q}}$-points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base with $s$ pinned to the cusp as in `hεbar`, there is a degree-zero divisor $D_v$ on `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ whose underlying divisor is the difference of the one-point divisors at the places attached to $x$ and to $s$, and such that the underlying morphism of $O.\mathrm{pts}(\,[D_v]\,)$ is $x$ followed by $\overline{\mathrm{aj}}$.
--
--   Finally, let $\varphi$ be a self-isomorphism of the fibre product of `toBase p (ΓM M H) hj` with `specMap (R p) ↥A` with `hφ` asserting that $\varphi$ followed by the structural morphism to $\operatorname{Spec} A$ is again that structural morphism, let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H`, and let `hφθ` assert that for all $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, if $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, $k_A$ and $\varphi$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and $k_A$, then the place attached to $y'$ is the image of the place attached to $y$ under the action of the semilinear automorphism `SemilinearAut.ofAlgAut θ`, that is, the pair $(\theta, \mathrm{id})$.
--
--   Under these hypotheses there exists a morphism $W$ from $G_A :=$ `RelativeGroupLaw.baseChangeStr Λ.σA O.g` to itself over $\operatorname{Spec} A$ such that both of the following hold.
--
--   First, $W$ is a homomorphism for the base-changed group law: for every scheme $T$, every $s : T \to \operatorname{Spec} A$ and all points $x, y$ of $G_A$ over $s$, the composite of $(O.L.\mathrm{baseChange}\,\Lambda.\sigma_A).\mathrm{mul}\,s\,x\,y$ with $W$ equals $(O.L.\mathrm{baseChange}\,\Lambda.\sigma_A).\mathrm{mul}\,s$ applied to the composites of $x$ with $W$ and of $y$ with $W$.
--
--   Second, $W$ realises the action of $\theta$ on $J_H(M)$ through the dictionary: for every $x \in J_H(M)$,
--   $$O.\mathrm{pts}\bigl(\mathrm{ofAlgAut}(\theta)\cdot x\bigr) = \mathrm{genOfBaseChangePt}\,\Lambda.h\sigma_A\bigl(\,\mathrm{baseChangePointOfBase}\,\Lambda.\sigma_A\bigl(\mathrm{castOver}\,\Lambda.h\sigma_A^{-1}\,(O.\mathrm{pts}\,x)\bigr)\ \text{followed by}\ W\bigr),$$
--   that is, the point $O.\mathrm{pts}\,x$ over $\mathrm{genPt}\,p$, reread as a point over $\mathrm{barPt}\,A$ followed by $\sigma_A$, lifted to a point of $G_A$ over $\mathrm{barPt}\,A$, composed with $W$, and pushed back down to a point over $\mathrm{genPt}\,p$, is $O.\mathrm{pts}$ of the image of $x$ under the semilinear automorphism attached to $\theta$.
--
--   This is the supply step producing an Atkin–Lehner type operator on the Néron object at $p$ from an automorphism of the Deligne–Rapoport model after base change to the valuation ring $A$: Picard functoriality at base $A$ converts the model automorphism $\varphi$, with its effect $\theta$ on the geometric function field, into an endomorphism $W$ of the base-changed group scheme compatible with the group law and with the dictionary of $\overline{\mathbb{Q}}$-points. It is used in the construction of the Fricke involution $w_M$ on $J_H(M)$ at $p$, whose factor $w_{M/p}$ is only defined after adjoining roots of unity contained in $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_ofAlgAut_of_baseChangeModelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_baseChange_abelJacobi.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_of_baseChangeModelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_baseChange_abelJacobi
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hL : O.L = RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD)

    [Algebra (R p) ↥A] (hσA_spec : specMap (R p) ↥A = Λ.σA)
    (hDA : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A))
    (hpoincA : Nonempty (hDA.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ↥A
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ↥A), pullback.condition⟩)).L))

    (hLA : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥A)) (x y : SchemeHomOver t' ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t' x y =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).baseChange (specMap (R p) ↥A)).mul t' x y)
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

    (φ : pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≅ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hφ : φ.hom ≫ baseChange (R p) (toBase p (ΓM M H) hj) ↥A = baseChange (R p) (toBase p (ΓM M H) hj) ↥A)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hφθ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ kA ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ kA →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
          (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
          (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W)) ∧
      (∀ x : JH M H, O.pts (SemilinearAut.ofAlgAut θ • x) =
        genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W)) := by sorry
