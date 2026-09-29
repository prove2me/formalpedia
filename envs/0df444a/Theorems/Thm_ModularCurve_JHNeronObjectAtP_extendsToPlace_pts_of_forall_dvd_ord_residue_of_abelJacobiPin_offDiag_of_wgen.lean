-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen
-- name    : ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/33eb749c-69d6-50d2-8a13-1b5c46e83695
-- title:
--   Divisibility of residue orders implies the class extends over A
-- statement:
--   Throughout, $p$ is a prime and $M$ a positive integer with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and $H \le (\mathbb Z/M)^\times$ is a subgroup containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$ (`hHp`); $M/p$ is nonzero. The hypothesis `hj` states that the $q$-series `jqModC ℚ` lies in the full-level $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb Q}$ of the intermediate field of $\mathbb Q$-Laurent series cut out at level $\Gamma_H(M)$, $F_{M/p}$ for the corresponding field at level $M/p$ for the image subgroup `infSubgroup p M H hpM` $= H \cdot \ker$, and $J_H(M) =$ `JH M H` $= \mathrm{Pic}^0(\overline{\mathbb Q}, F_M)$, the group of degree-zero divisor classes on places of $F_M$.
--
--   The geometric input is $\mathfrak X :$ `XHDRModelAtP p M H hpM hj`: a bundle of data for the two-chart integral model `toBase p (ΓM M H) hj` over the base ring `R p` (properness, flatness, integrality, local finite presentation, normality of affine charts, properness and relative smoothness at level `ΓN p M H hpM`), together with a curve model $\mathfrak X.\mathrm{Meta}$ over $\overline{\mathbb Q}$ with function field $F_M$, an isomorphism `𝔛.eeta` of it with the geometric fibre of the model, its Galois equivariance, the pinning of the chart coordinates and the generic-fibre smoothness and geometric integrality, among further fields (including the involution `𝔛.w`, the cusp section `𝔛.εinf`, the special-fibre curve model `𝔛.Mfib` with its component maps `𝔛.efib`, `𝔛.comp`, and the finite data used below).
--
--   Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime p`, i.e. $p$ is a nonunit of $A$; its residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed. $\Lambda$ is a `JHNeronObjectAtP.LevelData p M H hpM A`, consisting of a morphism $\sigma_A : \operatorname{Spec} A \to$ `base p` restricting to `genPt p` along `barPt A`, a scheme with structure morphism to `base p`, a relative group law on it, and parametrisations of its generic and special points by $\mathrm{Pic}^0$ at level $M/p$ and over $\kappa$. Finally $O$ is a `JHNeronObjectAtP p M H hpM A hA Λ`: a scheme $O.G$ with structure morphism $O.g$ to `base p`, a relative group law $O.L$ for `baseRing p`, a bijection $O.\mathrm{pts} : J_H(M) \simeq$ {sections of $O.g$ over `genPt p`}, the smoothness, separatedness, finite-type, quasi-compactness, surjectivity and fibre-connectedness of $O.g$, additivity and Galois equivariance of $O.\mathrm{pts}$, Hecke operators, flatness and surjectivity of multiplication by $n>0$, and the further fields of that structure, among them the finite set $O.\mathrm{ssFinset}$ of pairs of places of $\bar F =$ `Fbar p M H hpM κ` $=$ the $q$-expansion function field over $\kappa$ at level `ΓN p M H hpM`.
--
--   Let $\mathcal D$ denote the relative $\mathrm{Pic}^0$ designation $\langle O.G,\ O.g,\ (O.L.\mathrm{one}\,(\mathbf 1_{\operatorname{Spec}(R p)})).1 \rangle$, whose total space is $O.G$, whose structure morphism is $O.g$ and whose zero section is the identity element of the relative group law at the identity of $\operatorname{Spec}(R\,p)$.
--
--   **Representability hypotheses.** `hD` asserts that $\mathcal D$ represents, relative to the cusp section $\mathfrak X.\varepsilon_{\inf}$ and the condition `algEquivZeroCut` (rigidified line bundles that are fibrewise algebraically equivalent to zero on every geometric fibre), the relative sub-Picard functor of `toBase p (ΓM M H) hj` over `R p`: it supplies a Poincaré rigidified bundle satisfying the condition, the universal property that every such bundle on a base $T$ is the pullback of the Poincaré bundle along a unique $T$-point of $\mathcal D$, and the triviality of the pullback along the zero section. `hDQ` asserts the same for the base change of the model to $\mathbb Q$, the base-changed cusp section, and $\mathcal D$ base changed to $\mathbb Q$. `hsep` asserts that the generic fibre `baseChange (R p) (toBase p (ΓM M H) hj) ℚ` is separated, and `hpoinc` that the $\mathbb Q$-Poincaré bundle of `hDQ` is isomorphic to the bundle obtained from the Poincaré bundle of `hD` by pulling back along the first projection and descending through `BaseChange.ofR`.
--
--   **Abel–Jacobi hypotheses.** $\mathrm{aj}_{\mathbb Q}$ is a section over $\operatorname{Spec}\mathbb Q$ from the $\mathbb Q$-fibre of the model to the base-changed designation; `hajQε` says that the cusp section followed by $\mathrm{aj}_{\mathbb Q}$ is the zero section of $\mathcal D \otimes \mathbb Q$, and `hajQ` says that for every field $K$, every morphism $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb Q$ and every $t$-point $x$ of the $\mathbb Q$-fibre, the pullback of the $\mathbb Q$-Poincaré bundle along $x$ followed by $\mathrm{aj}_{\mathbb Q}$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the point $x$ with the ideal module of the relative effective Cartier divisor of the cusp at $t$; thus $\mathrm{aj}_{\mathbb Q}$ classifies $\mathcal O(x-\varepsilon)$. The morphism $k_{\mathbb Q}$ compares the geometric fibre with the $\mathbb Q$-fibre: `hkQ₁` and `hkQ₂` state that it commutes with the first projections and that its second projection is the second projection followed by $\operatorname{Spec}$ of $\mathbb Q \to \overline{\mathbb Q}$. Then $\overline{\mathrm{aj}} : \mathfrak X.\mathrm{Meta}.C \to O.G$ is required by `hajbar` to be $\mathfrak X.\mathrm{eeta}$ followed by $k_{\mathbb Q}$, by $\mathrm{aj}_{\mathbb Q}$ and by the first projection, and `hajbar_over` states that $\overline{\mathrm{aj}}$ followed by $O.g$ is $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$ followed by `genPt p`. The point $\bar\varepsilon$ is a $\overline{\mathbb Q}$-point of $\mathfrak X.\mathrm{Meta}.C$ (a section of its structure morphism); `hεbar` identifies it, through `eeta` and the first projection, with `genPt p` followed by the cusp section $\mathfrak X.\varepsilon_{\inf}$, and `hεbar_aj` states that $\bar\varepsilon$ followed by $\overline{\mathrm{aj}}$ is `genPt p` followed by the identity element of $O.L$. `hpts_law` states that $O.\mathrm{pts}$ is a homomorphism for the relative group law obtained from the representability `hD` through `algEquivZeroGroupCut`. `hAJ` states that for all $\overline{\mathbb Q}$-points $x, s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ equal to the cusp in the sense of `hεbar`, there is a degree-zero divisor $D_v$ on the places of $F_M$ equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ (via `𝔛.Meta.pointEquivPlace`) whose class satisfies $(O.\mathrm{pts}([D_v])).1 = x.1$ followed by $\overline{\mathrm{aj}}$.
--
--   **Degeneracy and transport hypotheses.** $\theta$ is a $\overline{\mathbb Q}$-algebra automorphism of $F_M$ and $\alpha : F_{M/p} \to F_M$ a $\overline{\mathbb Q}$-algebra map, with $\alpha$ integral (`hα`) and $\theta \circ \alpha$ integral (`hβ`); `hα_coe` states that $\alpha$ is the identity on the underlying Laurent series, and `hβ_coe` that $\theta \circ \alpha$ acts on Laurent series by `qExpand … p`, i.e. by $q \mapsto q^p$. `hwgen` pins $\theta$ to the involution $\mathfrak X.w$: for $\overline{\mathbb Q}$-points $y, y'$ of $\mathfrak X.\mathrm{Meta}.C$, if $y'$ composed with `eeta`, the first projection and $\mathfrak X.w.\mathrm{hom}$ equals $y$ composed with `eeta` and the first projection, then the place of $y'$ is the place of $y$ moved by the semilinear automorphism `SemilinearAut.ofAlgAut θ`. `hθgal` states that $\theta$ commutes with the arithmetic Galois action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $F_M$.
--
--   **Arithmetic of $A$.** $\rho : R\,p \to A$ is a ring homomorphism with $A.\mathrm{subtype} \circ \rho$ the structure map $R\,p \to \overline{\mathbb Q}$ (`hρ`), and `hσA` states that $\Lambda.\sigma_A$ is $\operatorname{Spec}$ of $\rho$. The unit $pb$ of $\mathbb Z/(M/p)$ has underlying residue $p$ (`hpb`), and the self-map $\delta$ of the places of $\bar F$ is, by `hδ`, the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`.
--
--   **Specialisation hypotheses.** $P_{sp}$ is a `JHPlaceSpecialization p M H hpM A`: a specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on $\mathrm{Pic}^0$, the compatibility of $\mathrm{sp}$ with orders of functions and $q$-expansions, surjectivity, the lifting of principal divisors, invariance under inertia, the Frobenius law for Frobenius elements at $p$, and the compatibility of the $\mathrm{Pic}^0$ map with push-forward of divisors. $R_{pd}$ is a `ProlongationDatum Psp θ`: two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue field $\bar F$, the residue-of-$q$-expansion law for $R_1$, and the statement that $R_2$ is $R_1$ transported by $\theta$. The hypotheses `hTD` (type dichotomy: for every place $W$ of $F_M$, either $\mathrm{reduceFst}_\alpha W$ is the $p$-power Frobenius image of $\mathrm{reduceSnd}_{\theta\alpha,\delta} W$, or $\delta$ of the Frobenius image of $\mathrm{reduceFst}_\alpha W$ equals $\mathrm{reduceSnd}_{\theta\alpha,\delta} W$), `hmodel` (`IsModel`, the conjunction of the two divisor laws and the two cusp laws), `hO` (`OrderLawFixed`, the order formula $\mathrm{mapDomain}(\mathrm{reduceFst})D$ at a $\delta$-fixed affine place as the sum of the $R_1$- and $R_2$-residue orders), `hRL` (`RegularityLaw` for $O.\mathrm{ssFinset}$) and `hNV` (`NodeValueLaw` for $O.\mathrm{ssFinset}$) are imposed for $\alpha$, $\theta \circ \alpha$, $\delta$.
--
--   Two compatibility hypotheses link the places of the special fibre with these reductions. In both, $i$ ranges over $\{0,1\}$, $y$ over $\overline{\mathbb Q}$-points of $\mathfrak X.\mathrm{Meta}.C$, $u$ over $A$-points of the model over $\operatorname{Spec}\rho$ with `barPt A` followed by $u$ equal to $y$ read through `eeta` and the first projection, $u_\kappa$ over $\kappa$-points of the fibre of the model along the residue map composed with $\rho$ that reduce $u$ and section the fibre structure map, and $P_0$ over closed points of the special-fibre curve model $\mathfrak X.\mathrm{Mfib}$ whose image under $\mathfrak X.\mathrm{efib}$ followed by the $i$-th component map is the closed point determined by $u_\kappa$. Then `hcompat` asserts that the place of $P_0$ is $P_{sp}.\mathrm{reduceFst}\,\alpha$ of the place of $y$ when $i=0$ and $P_{sp}.\mathrm{reduceSnd}\,(\theta\circ\alpha)\,\delta$ of the place of $y$ otherwise; `hcompat'` asserts, under the same data, that for $i=0$ one has $\mathrm{reduceSnd}_{\theta\alpha,\delta}(\text{place of } y) = \delta(\mathrm{Frob}_p(\text{place of } P_0))$, and otherwise $\mathrm{reduceFst}_\alpha(\text{place of } y) = \mathrm{Frob}_p(\text{place of } P_0)$, where $\mathrm{Frob}_p$ is `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`.
--
--   **The class and its root function.** Finally $n$ is a natural number with $0 < n$ (`hn`), $x \in J_H(M)$, $D$ a degree-zero divisor on the places of $F_M$ with class $x$ (`hDx`), and $f \in F_M$ satisfies $n \cdot D(W) = \mathrm{ord}_W f$ for every place $W$ (`hf`), lies in the valuation ring $R_{pd}.R_1.\mathrm{integers}$ (`h₁`) and has nonzero $R_1$-residue $\bar f = R_{pd}.R_1.\mathrm{residue}\langle f, h_1\rangle \in \bar F$ (`hr₁`).
--
--   **Conclusion.** If $n$ divides $\mathrm{ord}_{s.1}(\bar f)$ for every pair $s \in O.\mathrm{ssFinset}$ — the order of the reduced function $\bar f$ at the first place of each such pair — then `ExtendsToPlace A Λ.σA (O.pts x)` holds: there exists a section $s$ of $O.g$ over $\Lambda.\sigma_A$ such that the $\overline{\mathbb Q}$-point $(O.\mathrm{pts}\,x).1$ equals `barPt A` followed by $s$. Thus the point of $O$ attached to the class $x$ spreads out to an $A$-valued point of $O.G$.
--
--   This is the sufficiency half of the criterion, in Ribet's analysis of $J_H(M)$ at a prime $p$ exactly dividing $M$, for a degree-zero divisor class to have a point of the Deligne–Rapoport relative $\mathrm{Pic}^0$ above the valuation ring $A$: the reduction $\bar f$ of an $n$-th root function of the class has all its orders at the recorded pairs of places divisible by $n$. It feeds the equivalence [`ModularCurve.JHNeronObjectAtP.mem_finPts_iff_forall_ssPlacesQExp_dvd_ord_of_rootFunction_smul_of_coe_eq_coeffMap_residue_of_abelJacobiPin_of_algEquiv`](thm.html#ModularCurve.JHNeronObjectAtP.mem_finPts_iff_forall_ssPlacesQExp_dvd_ord_of_rootFunction_smul_of_coe_eq_coeffMap_residue_of_abelJacobiPin_of_algEquiv), and is proved from the corresponding statements for the model $\mathfrak X$ (existence of an annulus attached at both ends, goodness of the class, and extension of the Abel–Jacobi image) together with the principal-divisor and constant-field properties of $\bar F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen.lean

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

theorem ModularCurve.JHNeronObjectAtP.extendsToPlace_pts_of_forall_dvd_ord_residue_of_abelJacobiPin_offDiag_of_wgen
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

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ O.ssFinset)
    (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ O.ssFinset)

    (n : ℕ) (hn : 0 < n) (x : JH M H)
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (hDx : Pic0.mk D = x)
    (f : ↥(xHFunctionFieldBar M H))
    (hf : ∀ W, (n : ℤ) * (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) W = W.ord f)
    (h₁ : f ∈ Rpd.R₁.integers) (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) :
    (∀ s ∈ O.ssFinset, (n : ℤ) ∣ s.1.ord (Rpd.R₁.residue ⟨f, h₁⟩)) →
      ExtendsToPlace A Λ.σA (O.pts x) := by sorry
