-- Prove2me | Theorems.Thm_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge
-- name    : ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/c2a042d2-be61-59a1-8e10-1106c5a0be69
-- title:
--   Frobenius and Uₚ on the toric part of J₀(N₀p)[pⁿ]
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ satisfying `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$; consequently the residue field of $A$ has characteristic $p$. The groups $\mathrm{JZero}(N_0p) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{F}_{N_0p})$ and $\mathrm{JZero}(N_0)$ carry the module structures over the Hecke algebra $\mathtt{HeckeAlg} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ given by `heckeModuleBar`.
--
--   The assertion is made for every level datum $\Lambda$ of type `JZeroNeronObjectAtP.LevelData N₀ p A` satisfying `Λ.IsJacobian`, every Néron object $O$ of type `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, and every Deligne–Rapoport model package $\mathfrak{P}$ of type `DRModelPackageLevel N₀ p hpN₀`, under one hypothesis, which is the full existence-and-bridge statement for the triple $(\Lambda, O, \mathfrak{P})$ and consists of four conjuncts, described next.
--
--   **First conjunct: Abel–Jacobi pin.** Write $D$ for the relative $\mathrm{Pic}^0$-designation over $R_p$ whose total space is $O.G$, whose structure morphism is $O.g$ and whose zero section is the unit section $O.L.\mathrm{one}$ of the relative group law of $O$. It is required that there exist: data $h_D$ exhibiting $D$ as representing the rigidified relative Picard functor of $\mathtt{toBase}\ N_0\ p$ with rigidification along the cusp section $\mathfrak{P}.\varepsilon_{\inf}$, cut out by `algEquivZeroCut` (fibrewise algebraic equivalence to zero), i.e. a Poincaré rigidified line bundle over $D.\mathtt{toBase}$ satisfying that condition, universal among such bundles, and trivial along the zero section; the same datum $h_{DQ}$ after base change to $\mathbb{Q}$ for the base-changed designation $D.\mathtt{baseChange}\ \mathbb{Q}$ and the base-changed cusp section; an isomorphism $h_{PQ}$ between the Poincaré bundle of $h_{DQ}$ and the one obtained from that of $h_D$ by pulling back along the first projection and descending through `BaseChange.ofR`; separatedness of the base-changed curve over $\mathbb{Q}$; an Abel–Jacobi morphism $aj_Q$ over the $\mathbb{Q}$-fibre into $(D.\mathtt{baseChange}\ \mathbb{Q}).\mathtt{toBase}$ with $h_{ajQ\varepsilon}$ saying that it carries the cusp section to the zero section, and $h_{ajQ}$ saying that for every field $K$, every morphism $t \colon \operatorname{Spec} K \to \operatorname{Spec} \mathbb{Q}$ and every $K$-point $x$ of the curve over $t$, the Poincaré bundle of $h_{DQ}$ pulled back along $x$ followed by $aj_Q$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of the cusp section at $t$ (the class of $(x) - (\varepsilon_\infty)$); a comparison morphism $k_Q$ from the geometric-generic-point pullback to the $\mathbb{Q}$-pullback, compatible with the two projections ($h_{kQ1}$, $h_{kQ2}$); a morphism $ajbar$ from the curve $\mathfrak{P}.\mathtt{Meta}.C$ (the model of the function field $\overline{F}_{N_0p}$ over $\overline{\mathbb{Q}}$) to $D.P$, defined by $h_{ajbar}$ as $\mathfrak{P}.\mathtt{eeta}$ followed by $k_Q$, $aj_Q$ and the first projection, and lying over the generic point by $h_{ajbar\_over}$; and a $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ of $\mathfrak{P}.\mathtt{Meta}.C$ lying over the cusp section ($h_{\bar\varepsilon}$) and sent by $ajbar$ to the zero section ($h_{\bar\varepsilon\_aj}$). Subject to these data, two statements are required: the bijection $O.\mathtt{pts}$ from $\mathrm{JZero}(N_0p)$ to sections over the geometric generic point is additive for the relative group law obtained from $h_D$ through the group-theoretic cut `algEquivZeroGroupCut`; and for every pair of $\overline{\mathbb{Q}}$-points $x, s$ of $\mathfrak{P}.\mathtt{Meta}.C$ with $s$ lying over the cusp section, there is a degree-zero divisor $Dv$ on $\overline{F}_{N_0p}$ equal to $[\text{place of } x] - [\text{place of } s]$ under the bijection $\mathfrak{P}.\mathtt{Meta}.\mathtt{pointEquivPlace}$ between $\overline{\mathbb{Q}}$-points and places, whose class satisfies $(O.\mathtt{pts}(\mathrm{Pic}^0\text{-class of } Dv))_1 = x_1$ followed by $ajbar$.
--
--   **Second conjunct: special-fibre comparison.** It is required that there exist a ring homomorphism $\rho \colon R_p \to A$ compatible with the structure map to $\overline{\mathbb{Q}}$ and with $\Lambda.\sigma_A = \operatorname{Spec}(\rho)$; modular polynomial data `data` for $p$ together with the Kronecker congruence $h_{Kr}$, namely that the reduction of $\Phi$ modulo $p$ equals $(Y^p - X)(Y - X^p)$ in the bivariate sense used there; integrality hypotheses $h_\alpha$, $h_\beta$ for the two Hecke degeneracy embeddings $\overline{F}_{N_0} \to \overline{F}_{N_0p}$; a place specialisation $P$ of type `PlaceSpecialization A p N₀ data hKr (ResidueField A) (residue A) hα hβ`, a prolongation tuple $R_t$ for $P$ with $R_t.\mathtt{IsModel}$ (the four divisor and cusp laws), $R_t.\mathtt{RegularityLaw}$ and $R_t.\mathtt{NodeValueLaw}$ for the finite set $O.\mathtt{ssFinset}$ of places, and $R_t.\mathtt{OrderLawFixed}$; an additive map $sp$ from the inertia invariants of $\mathrm{JZero}(N_0p)$ (the elements fixed by `A.inertiaSubgroupIn ℚ`) to the glued $\mathrm{Pic}^0$ of the residue-field modular function field along the node pairs `nodePairsOfPlaces (arithFrobC p (ResidueField A) N₀) O.ssFinset`, with $P.\mathtt{IsGluedSpecialization}$ for $sp$; and an equality $h_E$ of the two intermediate fields `modularFunctionFieldC` and `modularFunctionFieldFullC` over the residue field of $A$. Subject to these, five statements are required: that $O.\mathtt{frob}$ equals the arithmetic Frobenius semilinear automorphism `arithFrobC p (ResidueField A) N₀`; two clauses identifying reductions of points, namely that for every $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{P}.\mathtt{Meta}.C$, every lift $u$ of it to a section over $\operatorname{Spec}(\rho)$, every section $u_\kappa$ of the fibre over the residue field compatible with $u$ and with the base, and assuming $P.\mathtt{IsStrictFst}$ or $P.\mathtt{IsStrictSnd}$ at the place of $y$, every closed point $P_0$ of the special-fibre curve $\mathfrak{P}.\mathtt{Mfib}$ whose image under $\mathfrak{P}.\mathtt{efib}$ is the image of the closed point under $u_\kappa$ followed by `fibreMap0 𝔓.π` has place $P.\mathtt{reduceFst}$ of the place of $y$, and the analogous clause with `fibreMap 𝔓.w.hom` inserted and $P.\mathtt{reduceSnd}$ in place of $P.\mathtt{reduceFst}$; the criterion that for $x$ in the inertia invariants, $O.\mathtt{pts}\,x$ extends to a section over $A$ (the predicate `ExtendsToPlace`) if and only if $P.\mathtt{IsGoodClass}$ holds for $x$ with respect to the node pairs; the compatibility that for $x$ in the inertia invariants and every section $s$ over $\Lambda.\sigma_A$ with $(O.\mathtt{pts}\,x)_1 = \mathtt{barPt}\ A$ followed by $s_1$, the pair formed from the two fibre components $O.\mathtt{abqFibre}\ 0$ and $O.\mathtt{abqFibre}\ 1$ of $s$, transported through $\Lambda.\mathtt{ptsSp}^{-1}$ and the $\mathrm{Pic}^0$-transport along the field identification $h_E$, equals `GluedPic0.toPic0Pair` of $sp\,x$; and the criterion that in the same situation the restriction of $s$ to the special fibre factors through the torus $O.\mathtt{torusFibre}$ of rank $O.\mathtt{toricRank}$ if and only if `toPic0Pair (sp x) = 0`.
--
--   **Third and fourth conjuncts: inertia clauses.** For every $m$ coprime to $p$, every $\sigma$ in `A.inertiaSubgroupIn ℚ` and every $m$-torsion point $x$ of $\mathrm{JZero}(N_0p)$, the difference $\sigma \cdot x - x$ lies in $O.\mathtt{toricPts}\ m$, the subgroup generated by the toric points of level $m$; and for every $m > 0$, every such $\sigma$ and every $m$-torsion $x$, the difference $\sigma \cdot x - x$ lies in $O.\mathtt{finPts}\ m$, the subgroup generated by those $m$-torsion points whose associated section extends over $A$.
--
--   **Conclusion.** Granting this hypothesis, for every $\mathbb{Q}$-algebra automorphism $\varphi$ of $\overline{\mathbb{Q}}$ which is a Frobenius at $A$ for $p$ (that is, $\varphi$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^p$), every $n \in \mathbb{N}$ and every $x \in O.\mathtt{toricPts}\,(p^n)$, the following three statements hold, where $c \in \mathbb{N}$ denotes the natural-number representative of the image of the $p$-adic cyclotomic character value $\chi_p(\varphi) \in \mathbb{Z}_p^{\times}$ in $\mathbb{Z}/p^n$, acting by natural-number scalar multiplication:
--
--   1. $\varphi \cdot x \in O.\mathtt{toricPts}\,(p^n)$;
--
--   2. $X_p \cdot (\varphi \cdot x) = c\, x$, where $X_p = \mathtt{heckeGen}\ p$ is the Hecke algebra generator at $p$;
--
--   3. $\varphi \cdot (X_p \cdot x) = c\, x$.
--
--   This is the levelwise law at $p$ for $J_0(N_0p)$ describing the interaction of a Frobenius element at a place above $p$ with the Hecke operator at $p$ on the toric part of the $p^n$-torsion: the toric part is Frobenius-stable, and both $U_p \varphi$ and $\varphi U_p$ act on it through the mod $p^n$ cyclotomic character. It is the input consumed by the Frobenius-value clause for the $q$-new eigenplane in the Tate module of $J_0$, used on the route to level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra
    ∀ (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (_ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
      (𝔓 : DRModelPackageLevel N₀ p hpN₀),
      (

      (let D : RelativePic0Designation (R p) (toBase N₀ p) :=
          ⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩
        ∃ (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
        (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
            (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
        (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
            (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

        (_ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

        (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
        (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
        (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
            (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
          Nonempty ((hDQ.poincare.pullbackAlong
              ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
              (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
                ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                  (Category.comp_id t)))).idealModule))

        (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
        (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
        (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

        (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
        (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
        (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
        (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection),

        (∀ x y : JZero (N₀ * p),
          O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧
        (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
          s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
              Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
            (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)) ∧

      (∃ (ρ : R p →+* ↥A) (_ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
          (_ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
          (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
          (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
          (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
          (Rt : PlaceSpecialization.ProlongationTuple P) (_ : Rt.IsModel) (_ : Rt.RegularityLaw O.ssFinset)
          (_ : Rt.NodeValueLaw O.ssFinset) (_ : Rt.OrderLawFixed)
          (sp : ↥(inertiaInvariants A (N₀ * p)) →+
            GluedPic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset))
          (_ : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) sp)

          (hE : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀),

        O.frob = arithFrobC p (ResidueField ↥A) N₀ ∧

        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 =
                (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y)) ∧
        (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
            (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
            (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
            (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
            (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
            (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
            (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
            (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P1.1 =
                (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base
                  (IsLocalRing.closedPoint (ResidueField ↥A)) →
              (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y)) ∧

        (∀ x : ↥(inertiaInvariants A (N₀ * p)),
          ExtendsToPlace A Λ.σA (O.pts (x : JZero (N₀ * p))) ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (x : JZero (N₀ * p))) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver Λ.σA O.g),
          (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) s))),
            (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm (Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) s)))) =
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (sp x)) ∧

        (∀ (x : ↥(inertiaInvariants A (N₀ * p))) (s : SchemeHomOver Λ.σA O.g),
          (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1 →
          ((∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) O.toricRank),
              NeronModelInfra.schemeHomOverComp y O.torusFibre = toFibrePt (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) s)) ↔
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset) (sp x) = 0))) ∧

      (∀ (m : ℕ), m.Coprime p →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.toricPts m) ∧
      (∀ (m : ℕ), 0 < m →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.finPts m)) →
      ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ p →
        ∀ (n : ℕ), ∀ x ∈ O.toricPts (p ^ n),
          φ • x ∈ O.toricPts (p ^ n) ∧
          (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • (φ • x) =
            (PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val • x ∧
          φ • ((heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • x) =
            (PadicInt.toZModPow n ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val • x := by sorry
