-- Prove2me | Theorems.Thm_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne
-- name    : ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/e330868d-1158-5701-882a-9242df84fb0e
-- title:
--   Frobenius and Uₚ on prime-to-p toric torsion
-- statement:
--   Fix a natural number $N_0$ (nonzero) and a prime $p$ with $p \nmid N_0$, and let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ such that $A.\mathrm{LiesOverPrime}\ p$ holds, i.e. $p$ is a nonunit of $A$; consequently the residue field of $A$ has characteristic $p$. The ambient structures used throughout are the Hecke-algebra module structures `heckeModuleBar (N₀ * p)` and `heckeModuleBar N₀` on $\mathrm{Pic}^0$ of the modular function fields of levels $N_0p$ and $N_0$ over $\overline{\mathbb{Q}}$ (defined by evaluation of `HeckeAlg = MvPolynomial Nat.Primes ℤ` at the Hecke operators when these commute, and trivially otherwise), decidable equality on the residue field of $A$, and the two algebra structures of `modularFunctionFieldFullC (ResidueField ↥A) N₀` over the residue field.
--
--   The statement is quantified over: a level datum $\Lambda$ of type `JZeroNeronObjectAtP.LevelData N₀ p A` (a morphism $\sigma_A : \mathrm{Spec}\,A \to$ `base p` lifting the geometric generic point, a scheme $X$ over `base p` with a relative group law, and bijections `pts` from `JZero N₀` to the sections over the geometric generic point and `ptsSp` from the level-$N_0$ $\mathrm{Pic}^0$ over the residue field to the sections over $\mathrm{Spec}$ of the residue field); a hypothesis $\Lambda.\mathrm{IsJacobian}$ (the abelian-scheme property bundle for $\Lambda.f$, commutativity of the group law, additivity and Galois equivariance of `pts`, additivity of `ptsSp`, agreement of reduction of points under the mod-$\ell$ reduction inputs, and realisability of every Hecke operator by an endomorphism of $\Lambda.f$); an object $O$ of type `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ` (a smooth, separated, locally of finite type, quasi-compact, surjective scheme $G$ over `base p` with connected fibres and a commutative relative group law $L$, a bijection `pts` from `JZero (N₀ * p)` to the sections over the geometric generic point which is additive, Galois-equivariant and compatible with the Hecke action, flatness and surjectivity of multiplication by positive integers, properness of the generic fibre, together with the further data recorded in $O$: its toric rank, the semilinear automorphism $O.\mathrm{frob}$, the finite set $O.\mathrm{ssFinset}$ of places, the fibre morphisms $O.\mathrm{abqFibre}\ 0$, $O.\mathrm{abqFibre}\ 1$, $O.\mathrm{torusFibre}$ and the toric points $O.\mathrm{toricPoint}$); and a Deligne–Rapoport model package $\mathfrak{P}$ of type `DRModelPackageLevel N₀ p hpN₀` for the Igusa-type morphism `toBase N₀ p` $: X_{N_0,p} \to \mathrm{Spec}\,(R\,p)$, which carries in particular a curve model $\mathfrak{P}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `modularFunctionFieldBar (N₀ * p)`, the isomorphism $\mathfrak{P}.\mathrm{eeta}$ identifying it with the geometric generic fibre, the sections $\mathfrak{P}.\varepsilon_{\inf}$ and $\mathfrak{P}.\varepsilon_{\mathrm{zero}}$, the involution $\mathfrak{P}.w$, the degeneracy $\mathfrak{P}.\pi$, and the special-fibre curve models $\mathfrak{P}.\mathrm{Mfib}$ with the morphism $\mathfrak{P}.\mathrm{efib}$.
--
--   The single antecedent is a conjunction of four groups of conditions, summarised here group by group.
--
--   (A) *Abel–Jacobi representability.* With $D$ the relative $\mathrm{Pic}^0$ designation over $R\,p$ whose total space is $O.G$, whose structure morphism is $O.g$ and whose zero section is the unit section of the relative group law $O.L$ at the identity of $\mathrm{Spec}\,(R\,p)$, there exist: a proof $hD$ that $D$ represents the relative sub-Picard functor of `toBase N₀ p` rigidified along $\mathfrak{P}.\varepsilon_{\inf}$ for the condition `algEquivZeroCut` (rigidified line bundles that are fibrewise algebraically equivalent to zero); the corresponding representability $hDQ$ after base change to $\mathbb{Q}$, for the base-changed section and the base-changed designation $D.\mathrm{baseChange}\ \mathbb{Q}$; an isomorphism $hPQ$ between the Poincaré bundle of $hDQ$ and the descent to $\mathbb{Q}$ of the pullback of the Poincaré bundle of $hD$ along the first projection; separatedness of the base change of `toBase N₀ p` to $\mathbb{Q}$; an Abel–Jacobi morphism $ajQ$ over the $\mathbb{Q}$-curve to $(D.\mathrm{baseChange}\ \mathbb{Q}).\mathrm{toBase}$ taking the base-changed cusp section to the zero section ($hajQ\varepsilon$) and satisfying, for every field $K$, every $\mathbb{Q}$-point $t$ of $\mathrm{Spec}\,K$ and every $K$-point $x$ of the $\mathbb{Q}$-curve, an isomorphism between the pullback of the $hDQ$-Poincaré bundle along $x$ followed by $ajQ$ and the tensor product of the line bundle of the relative effective Cartier divisor of $x$ with the ideal module of the divisor of $t$ followed by the base-changed cusp section ($hajQ$); a morphism $kQ$ from the geometric generic fibre pullback to the $\mathbb{Q}$-fibre pullback compatible with the first projections ($hkQ_1$) and with the second projections up to $\mathrm{Spec}\,\mathbb{Q} \to \mathrm{Spec}\,\overline{\mathbb{Q}}$ ($hkQ_2$); a geometric Abel–Jacobi morphism $\overline{aj} : \mathfrak{P}.\mathrm{Meta}.C \to D.P$ equal to $\mathfrak{P}.\mathrm{eeta}$ followed by $kQ$, $ajQ$ and the first projection ($h\overline{aj}$), lying over $\mathfrak{P}.\mathrm{Meta}.\mathrm{toBase}$ followed by the geometric generic point ($h\overline{aj}\_over$); and a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $\mathfrak{P}.\mathrm{Meta}.C$ over the base lying over $\mathfrak{P}.\varepsilon_{\inf}$ ($h\overline{\varepsilon}$) and carried by $\overline{aj}$ to the zero section ($h\overline{\varepsilon}\_aj$). Subject to these data, two assertions are required: first, $O.\mathrm{pts}$ is additive for the relative group law attached to $hD$ by the group-theoretic refinement `algEquivZeroGroupCut` of the condition, that is $O.\mathrm{pts}(x+y)$ is the product of $O.\mathrm{pts}(x)$ and $O.\mathrm{pts}(y)$ for all $x,y \in$ `JZero (N₀ * p)`; secondly, for every pair of $\overline{\mathbb{Q}}$-points $x,s$ of $\mathfrak{P}.\mathrm{Meta}.C$ over the base with $s$ lying over $\mathfrak{P}.\varepsilon_{\inf}$, there is a degree-zero divisor $Dv$ on the function field `modularFunctionFieldBar (N₀ * p)` equal to $[\,\mathfrak{P}.\mathrm{Meta}.\mathrm{pointEquivPlace}\ x\,] - [\,\mathfrak{P}.\mathrm{Meta}.\mathrm{pointEquivPlace}\ s\,]$ whose class satisfies $O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of }Dv) = x$ followed by $\overline{aj}$.
--
--   (B) *Reduction and gluing data at $p$.* There exist: a ring homomorphism $\rho : R\,p \to A$ whose composite with the inclusion of $A$ is the structure map $R\,p \to \overline{\mathbb{Q}}$, and with $\Lambda.\sigma_A = \mathrm{Spec}\,\rho$; modular polynomial data for $p$ together with the Kronecker congruence for it; integrality hypotheses $h\alpha$ and $h\beta$ for the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of levels $N_0, p$ over $\overline{\mathbb{Q}}$; a place specialization $P$ relative to $A$, $p$, $N_0$, these data, the residue field of $A$ and its residue map; a prolongation tuple $Rt$ for $P$ which is a model ($Rt.\mathrm{IsModel}$: the two divisor laws and the two cusp laws) and satisfies the regularity law and the node-value law for the finite set $O.\mathrm{ssFinset}$ of places as well as the fixed-order law; an additive map $sp$ from the inertia invariants of `JZero (N₀ * p)` (the elements fixed by the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$) to the glued $\mathrm{Pic}^0$ of the residue field and `modularFunctionFieldC` for the node pairs `nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) O.ssFinset`, which is a glued specialization for $P$; and an equality $hE$ between `modularFunctionFieldC (ResidueField ↥A) N₀` and `modularFunctionFieldFullC (ResidueField ↥A) N₀`. Subject to these, six assertions are required: (B1) $O.\mathrm{frob}$ equals the arithmetic Frobenius semilinear automorphism `arithFrobC p (ResidueField ↥A) N₀`; (B2) and (B3) for every $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{P}.\mathrm{Meta}.C$ over the base, every section $u$ of `toBase N₀ p` over $\mathrm{Spec}\,\rho$ whose geometric specialisation is $y$, every residue-field point $u\kappa$ of the fibre over $\mathrm{residue}\circ\rho$ which reduces $u$ and is a section of the fibre, and under the alternative that the place of $y$ is $P$-strict on the first or on the second branch, every closed point $P_0$ of the special-fibre curve model $\mathfrak{P}.\mathrm{Mfib}$ whose image under $\mathfrak{P}.\mathrm{efib}$ is the image of the closed point under $u\kappa$ followed by `fibreMap0 𝔓.π` has place $P.\mathrm{reduceFst}$ of the place of $y$; and likewise every closed point $P_1$ whose image under $\mathfrak{P}.\mathrm{efib}$ is the image of the closed point under $u\kappa$ followed by the fibre map of $\mathfrak{P}.w$ and then `fibreMap0 𝔓.π` has place $P.\mathrm{reduceSnd}$ of the place of $y$; (B4) for $x$ in the inertia invariants, the section $O.\mathrm{pts}(x)$ extends to a section over $\mathrm{Spec}\,A$ along $\Lambda.\sigma_A$ if and only if $x$ is a good class for $P$ with respect to the node pairs; (B5) for $x$ in the inertia invariants and $s$ a section of $O.g$ over $\Lambda.\sigma_A$ with $O.\mathrm{pts}(x)$ the geometric point followed by $s$, the pair of $\mathrm{Pic}^0$ classes obtained by transporting, via the isomorphism of function fields given by $hE$ and the inverse of $\Lambda.\mathrm{ptsSp}$, the two fibre restrictions of $s$ along $O.\mathrm{abqFibre}\ 0$ and $O.\mathrm{abqFibre}\ 1$ equals the image of $sp(x)$ under `GluedPic0.toPic0Pair`; (B6) under the same hypotheses on $x$ and $s$, the reduction of $s$ comes from a point of the split torus of rank $O.\mathrm{toricRank}$ over the residue field (there is a $y$ with $y$ followed by $O.\mathrm{torusFibre}$ equal to the fibre point of $s$) if and only if `toPic0Pair (sp x) = 0`.
--
--   (C) *Toric approximation of inertia on prime-to-$p$ torsion.* For every $m$ coprime to $p$, every $\sigma$ in the image of the inertia subgroup of $A$ over $\mathbb{Q}$ and every $m$-torsion element $x$ of `JZero (N₀ * p)`, the difference $\sigma \cdot x - x$ lies in $O.\mathrm{toricPts}\ m$, the subgroup generated by the toric points of order dividing $m$.
--
--   (D) *Approximation by the finite part.* For every $m > 0$, every $\sigma$ in the image of the inertia subgroup and every $m$-torsion element $x$, the difference $\sigma \cdot x - x$ lies in $O.\mathrm{finPts}\ m$, the subgroup generated by those $m$-torsion classes whose section extends over $\mathrm{Spec}\,A$.
--
--   Under this antecedent the conclusion is: for every automorphism $\varphi$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which is a Frobenius at $A$ for $p$ (that is, $\varphi$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{p}$), for every prime $\ell \neq p$, every $k \in \mathbb{N}$ and every $x \in O.\mathrm{toricPts}(\ell^{k})$:
--   $$\varphi \cdot x \in O.\mathrm{toricPts}(\ell^{k}), \qquad T_p \cdot (\varphi \cdot x) = p\,x, \qquad \varphi \cdot (T_p \cdot x) = p\,x,$$
--   where $T_p$ denotes the generator `heckeGen ⟨p, _⟩` of `HeckeAlg` at $p$ acting through the module structure `heckeModuleBar (N₀ * p)`, and $p\,x$ is the $p$-fold sum of $x$.
--
--   At level $\Gamma_0(N_0p)$ this is the Eichler–Shimura relation in its multiplicative-reduction form: on the toric part of the $\ell$-power torsion of the Néron object at $p$, the Hecke generator at $p$ and a Frobenius element at $p$ compose, in either order, to multiplication by $p$, and the toric subgroup is Frobenius-stable. It feeds the statement [`ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge`](thm.html#ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_of_isFrobeniusAt_of_bridge), and thence the level-lowering analysis of the inertia action at $p$ on the Jacobian of $X_0(N_0p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne.lean

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

theorem ModularCurve.jZeroNeronObjectAtP_smul_mem_toricPts_and_heckeGen_smul_eq_and_smul_heckeGen_eq_of_isFrobeniusAt_of_ne
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
        ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
        ∀ (k : ℕ), ∀ x ∈ O.toricPts (ℓ ^ k),
          φ • x ∈ O.toricPts (ℓ ^ k) ∧
          (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • (φ • x) = p • x ∧
          φ • ((heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • x) = p • x := by sorry
