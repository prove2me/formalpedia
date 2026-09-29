-- Prove2me | Theorems.Thm_ModularCurve_exists_jZeroNeronObjectAtP_and_bridge
-- name    : ModularCurve.exists_jZeroNeronObjectAtP_and_bridge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/49f6c337-0133-558d-ba87-b7ae0977e1b0
-- title:
--   Néron object of J₀(N₀p) at p with its bridges
-- statement:
--   Throughout, $N_0\ge 1$ and $p$ is a prime with $p\nmid N_0$, and $A$ is a valuation subring of $\overline{\mathbf Q}$ satisfying `A.LiesOverPrime p`, that is $p$ lies in `A.nonunits`; consequently the residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $p$ (this instance is produced from [`ValuationSubring.charP_residueField_of_liesOverPrime_def`](def/WeierstrassCurve_ReductionMap.html#L57)). The statement is made with the Hecke-algebra module structures `heckeModuleBar` on $J_0$-groups at levels $N_0p$ and $N_0$ in force, where `JZero N` denotes $\mathrm{Pic}^0$ over $\overline{\mathbf Q}$ of `modularFunctionFieldBar N` (the base change to $\overline{\mathbf Q}$ of the full level-$N$ modular function field), together with the decidability instance for $\kappa$ and the algebra structures of $\kappa$ on `modularFunctionFieldC κ N₀` and on `modularFunctionFieldFullC κ N₀`.
--
--   The assertion is the existence of: a level datum $\Lambda$ of type `JZeroNeronObjectAtP.LevelData N₀ p A` (an $A$-point $\Lambda.\sigma_A$ of the base $\operatorname{Spec}$ of the local base ring at $p$ whose composite with `barPt A` is `genPt p`, a scheme $\Lambda.X$ over that base carrying a relative group law $\Lambda.L$, a bijection $\Lambda.\mathrm{pts}$ from `JZero N₀` onto the points over `genPt p`, and a bijection $\Lambda.\mathrm{ptsSp}$ from `JZeroC κ N₀` onto the points over `resPt A ≫ Λ.σA`); a proof that $\Lambda$ is a Jacobian in the sense of `LevelData.IsJacobian`, i.e. $\Lambda.f$ carries the abelian-scheme property bundle `AbelianSchemePropertyBundle` over the base ring, the group law is commutative, both dictionaries $\Lambda.\mathrm{pts}$ and $\Lambda.\mathrm{ptsSp}$ are additive, $\Lambda.\mathrm{pts}$ is equivariant for the action of $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ by base change of points, the predicate `ReductionInputsModL A N₀` implies `ReductionOfPointsAgreesModL`, and every element of the Hecke algebra is realised by an endomorphism of $\Lambda.f$ over the base which is additive for $\Lambda.L$ and matches the Hecke action on `JZero N₀`; a Néron object $O$ of type `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ` (in particular a smooth, separated, surjective group-like scheme $g\colon G\to\operatorname{Spec}$ of the base with commutative relative group law $O.L$, a bijection $O.\mathrm{pts}$ from `JZero (N₀ * p)` onto the points over `genPt p` that is additive, Galois-equivariant and Hecke-equivariant, flat and surjective multiplication by each positive integer, proper generic fibre, a toric rank, a finset $O.\mathrm{ssFinset}$ of places of `modularFunctionFieldC κ N₀`, a semilinear automorphism $O.\mathrm{frob}$, special-fibre data $O.\mathrm{abqFibre}$ and $O.\mathrm{torusFibre}$, and toric points); and a Deligne–Rapoport model package $\mathfrak P$ of type `DRModelPackageLevel N₀ p hpN₀` for the Igusa model `toBase N₀ p` of level $N_0p$ over the base ring `R p` (properness, flatness, integrality and local finite presentation of that morphism, normality of its affine charts, a curve model $\mathfrak P.\mathrm{Meta}$ of `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$ with an isomorphism $\mathfrak P.\mathrm{eeta}$ onto the geometric generic fibre compatible with the Galois action and pinned on the Igusa charts, smoothness and geometric integrality of the generic fibre, and the sections $\mathfrak P.\varepsilon_\infty$, $\mathfrak P.\varepsilon_0$ together with the further degeneracy and special-fibre data of that structure), such that the following three groups of statements hold.
--
--   First (the Abel–Jacobi block). Let $D$ be the relative $\mathrm{Pic}^0$ designation read off $O$: underlying scheme $O.G$, structure morphism $O.g$, zero section the unit section of $O.L$ at the identity of the base. Then there exist: a witness `hD` that $D$ represents the subfunctor of the rigidified relative Picard functor of `toBase N₀ p` rigidified along $\mathfrak P.\varepsilon_\infty$ and cut out by `algEquivZeroCut`, the condition that a rigidified line bundle be fibrewise algebraically equivalent to zero (a Poincaré rigidified bundle satisfying the condition, the universal property classifying every such bundle by a unique morphism over the base up to isomorphism of line bundles, and triviality along the zero section); a witness `hDQ` of the same representability statement after base change of the model, its $\infty$-section and $D$ to $\mathbf Q$; an isomorphism `hPQ` between the Poincaré bundle of `hDQ` and the base change to $\mathbf Q$ of the pullback of the Poincaré bundle of `hD` along the first projection of $D$ base-changed; a proof that `baseChange (R p) (toBase N₀ p) ℚ` is separated; a morphism $\mathrm{aj}_{\mathbf Q}$ from the generic fibre of the model to the generic fibre of $D$ over $\operatorname{Spec}\mathbf Q$, with `hajQε` asserting that the $\infty$-section followed by $\mathrm{aj}_{\mathbf Q}$ is the zero section of $D$ base-changed, and `hajQ` asserting that for every field $K$, every $t\colon\operatorname{Spec}K\to\operatorname{Spec}\mathbf Q$ and every $K$-point $x$ of the generic fibre over $t$, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by $\mathrm{aj}_{\mathbf Q}$ is isomorphic to the tensor product of the line bundle (inverse ideal module) of the degree-one relative effective Cartier divisor cut out by the graph of $x$ with the ideal module of the one cut out by $t$ followed by the base-changed $\infty$-section; a comparison morphism $k_{\mathbf Q}$ from the geometric generic fibre to the generic fibre, with `hkQ₁` and `hkQ₂` saying that it commutes with the first projections and, on second projections, with $\operatorname{Spec}\overline{\mathbf Q}\to\operatorname{Spec}\mathbf Q$; a morphism $\overline{\mathrm{aj}}\colon \mathfrak P.\mathrm{Meta}.C\to D.P$, with `hajbar` identifying it as $\mathfrak P.\mathrm{eeta}$ followed by $k_{\mathbf Q}$, by $\mathrm{aj}_{\mathbf Q}$ and by the first projection, and `hajbar_over` saying that $\overline{\mathrm{aj}}$ followed by $D.\mathrm{toBase}$ equals $\mathfrak P.\mathrm{Meta}.\mathrm{toBase}$ followed by `genPt p`; and a $\overline{\mathbf Q}$-point $\overline\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ (a section of its structure morphism) with `hεbar` saying that it lies over the $\infty$-section of the model and `hεbar_aj` that $\overline\varepsilon$ followed by $\overline{\mathrm{aj}}$ is `genPt p` followed by the zero section of $D$. For these data two assertions hold: $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD` through `algEquivZeroGroupCut`, that is $O.\mathrm{pts}(x+y)$ is the product of $O.\mathrm{pts}(x)$ and $O.\mathrm{pts}(y)$ for all $x,y\in$ `JZero (N₀ * p)`; and for all $\overline{\mathbf Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ lying over the $\infty$-section as in `hεbar`, there is a degree-zero divisor $D_v$ on `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbf Q}$ equal to the difference of the one-point divisors at the places $\mathfrak P.\mathrm{Meta}.\mathrm{pointEquivPlace}(x)$ and $\mathfrak P.\mathrm{Meta}.\mathrm{pointEquivPlace}(s)$, whose class satisfies $O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of }D_v)=x$ followed by $\overline{\mathrm{aj}}$.
--
--   Second (the specialisation block). There exist: a ring homomorphism $\rho\colon$ `R p` $\to A$ whose composite with the inclusion of $A$ is the structure map of $\overline{\mathbf Q}$ and with $\Lambda.\sigma_A=\operatorname{Spec}\rho$; modular polynomial data `data` at $p$ (a monic $\Phi$ of degree $\psi(p)$ annihilating the pair $(j,j_p)$) together with a Kronecker congruence `hKr`, i.e. the reduction of $\Phi$ modulo $p$ equals $(\mathrm{C}\,X^{p}-X)(\mathrm{C}\,X-X^{p})$; integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` at level $(N_0,p)$ over $\overline{\mathbf Q}$; a place specialisation $P$ of type `PlaceSpecialization A p N₀ data hKr κ (residue A) hα hβ`, which in particular provides a map of places of `modularFunctionFieldBar N₀` to places of `modularFunctionFieldC κ N₀` and, via restriction along the two degeneracy embeddings, the two reductions $P.\mathrm{reduceFst}$, $P.\mathrm{reduceSnd}$ of places of the level-$N_0p$ field; a prolongation tuple $R_t$ for $P$ (two regular prolongations of $A$ in `modularFunctionFieldBar (N₀ * p)` with residue field `modularFunctionFieldFullC κ N₀`, a residue map $\overline{\mathrm{red}}$ and an embedding $\iota$, with their compatibilities) satisfying $R_t.\mathrm{IsModel}$ (the two divisor laws and the two cusp laws), $R_t.\mathrm{RegularityLaw}$ and $R_t.\mathrm{NodeValueLaw}$ for the finset $O.\mathrm{ssFinset}$, and $R_t.\mathrm{OrderLawFixed}$ (these laws relate orders and values of the two residues of a function at Frobenius-stable affine geometric places and at node pairs; their clauses are as in the corresponding definitions); a homomorphism $\mathrm{sp}$ from the inertia invariants `inertiaInvariants A (N₀ * p)` — the invariants of `JZero (N₀ * p)` under the image `A.inertiaSubgroupIn ℚ` of the inertia subgroup of $A$ — to the glued $\mathrm{Pic}^0$ group of $\kappa$ and `modularFunctionFieldC κ N₀` for the node pairs `nodePairsOfPlaces (arithFrobC p κ N₀) O.ssFinset` obtained from $O.\mathrm{ssFinset}$ by the coefficientwise arithmetic Frobenius, together with the assertion that $\mathrm{sp}$ is a glued specialisation for $P$ (for every degree-zero divisor whose class is inertia-invariant and is a good divisor for $P$, and every admissible gluing datum equal to $P.\mathrm{glueData}$ of it, $\mathrm{sp}$ sends the class to the class of that datum); and an equality `hE` of the intermediate fields `modularFunctionFieldC κ N₀` and `modularFunctionFieldFullC κ N₀`. For these data, five assertions hold: $O.\mathrm{frob}$ equals `arithFrobC p κ N₀`; for every $\overline{\mathbf Q}$-point $y$ of $\mathfrak P.\mathrm{Meta}.C$, every $A$-point $u$ of the model reducing to $y$ in the stated sense, every $\kappa$-point $u_\kappa$ of the fibre along $\mathrm{residue}\circ\rho$ compatible with $u$ and sectional for the second projection, and under the alternative that the place of $y$ is strict for the first or for the second reduction, every closed point $P_0$ of the special-fibre curve model $\mathfrak P.\mathrm{Mfib}$ whose image under $\mathfrak P.\mathrm{efib}$ is the image of the closed point of $\kappa$ under $u_\kappa$ followed by the degeneracy fibre map `fibreMap0 𝔓.π` has $\mathfrak P.\mathrm{Mfib}.\mathrm{placeOfPoint}(P_0)=P.\mathrm{reduceFst}$ of the place of $y$; the same statement with the Atkin–Lehner fibre map `fibreMap 𝔓.w.hom 𝔓.w_over` inserted before `fibreMap0 𝔓.π`, concluding instead $\mathfrak P.\mathrm{Mfib}.\mathrm{placeOfPoint}(P_1)=P.\mathrm{reduceSnd}$ of that place; for every inertia-invariant class $x$, the point $O.\mathrm{pts}(x)$ extends to a point over $\Lambda.\sigma_A$ (the predicate `ExtendsToPlace`) if and only if $x$ is a good class for $P$ relative to those node pairs; for every inertia-invariant $x$ and every point $s$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}(x)=$ `barPt A` followed by $s$, the pair obtained by reducing $s$ to $\kappa$, applying the two special-fibre maps $O.\mathrm{abqFibre}\,0$ and $O.\mathrm{abqFibre}\,1$, inverting $\Lambda.\mathrm{ptsSp}$ and transporting along the $\mathrm{Pic}^0$ isomorphism induced by `hE` equals `GluedPic0.toPic0Pair` of $\mathrm{sp}(x)$; and, for the same $x$ and $s$, the reduction of $s$ comes from a $\kappa$-point of the split torus of rank $O.\mathrm{toricRank}$ through $O.\mathrm{torusFibre}$ if and only if `GluedPic0.toPic0Pair` of $\mathrm{sp}(x)$ is zero.
--
--   Third (the inertia clauses). For every $m$ coprime to $p$, every $\sigma$ in `A.inertiaSubgroupIn ℚ` and every $m$-torsion class $x$ of `JZero (N₀ * p)`, the difference $\sigma\cdot x-x$ lies in $O.\mathrm{toricPts}\,m$, the subgroup generated by the toric points of $O$ at level $m$; and for every $m>0$, every such $\sigma$ and every $m$-torsion class $x$, the difference $\sigma\cdot x-x$ lies in $O.\mathrm{finPts}\,m$, the subgroup generated by those $m$-torsion classes whose associated point extends to a point over $\Lambda.\sigma_A$.
--
--   This is the existence step that builds, at a prime $p$ not dividing $N_0$ and at a chosen place $A$ of $\overline{\mathbf Q}$ above $p$, the level-$N_0p$ Néron object of $J_0(N_0p)$ together with the bridges that make it usable: the Abel–Jacobi normalisation of its points dictionary against a Deligne–Rapoport model, the comparison of its special fibre with the glued $\mathrm{Pic}^0$ of two copies of the level-$N_0$ curve over $\kappa$ in Raynaud's form, and the inertia (monodromy) clauses. It is the input to the statements bounding the monodromy span on eigenplanes of Tate modules of $J_0$ and to the further packaging of Néron data at $p$ used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_jZeroNeronObjectAtP_and_bridge.lean

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

theorem ModularCurve.exists_jZeroNeronObjectAtP_and_bridge
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    letI : Algebra (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N₀) :=
      (modularFunctionFieldFullC (ResidueField ↥A) N₀).algebra
    ∃ (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (_ : Λ.IsJacobian) (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

      (𝔓 : DRModelPackageLevel N₀ p hpN₀),

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
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ jZeroTorsion (N₀ * p) m, σ • x - x ∈ O.finPts m) := by sorry
