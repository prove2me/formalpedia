-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero
-- name    : ModularCurve.DRResolvedModelPackage.multidegree_mem_range_intersectionAlpha_of_comp_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/2520e7fa-44bd-5c66-9416-c9504ef13a05
-- title:
--   Vanishing component class puts the multidegree in α's image
-- statement:
--   Fix a prime $p$ and a package `DRModelPackage p` $\mathfrak{X}$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed perfect field $k$ of characteristic $p$ with a ring homomorphism $red : A \to k$, modular polynomial data `data` for $p$ satisfying the Kronecker congruence $hKr$, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings of the level‑$1$ into the level‑$p$ function field, and a place specialisation $P$ for these data. Let $W$ be a finite set of places of `modularFunctionFieldC k 1` whose members are exactly the supersingular places `ssPlaces p 1 k`, let $e$ assign a width to each such place, let `depth` assign a natural number to each place of `modularFunctionFieldBar (1 * p)`, and let `comp` be an additive map from the inertia invariants $\mathrm{JZero}(1\cdot p)^{I_A}$ to the component group of the width function `widthOfPlaces (arithFrobC p k 1) W e`, satisfying $P$'s depth–component law `hlaw`: for every admissible inertia‑stable degree‑zero divisor $D$ and every node pair $s_0$, `comp` of the class of $D$ is the image in the component group of the depth functional of $D$ plus the degree of the strict‑second part of $D$ times $e(s_0)$ times the crossing coordinate of $s_0$. Let further $O$ be a commutative ring with $to\kappa : O \to k$, let $\mathfrak{X}reg$ be a resolved model package `DRResolvedModelPackage p 𝔛 O k toκ`, let $\sigma N : W \simeq \mathfrak{X}reg.\mathrm{node}$ match widths, i.e. $\mathfrak{X}reg.width(\sigma N(w)) = e(w)$, and let `swap` be a Boolean. Assume given $x$ in the inertia invariants with $\mathrm{comp}(x) = 0$, a degree‑zero divisor $D_0$ whose class in $\mathrm{Pic}^0$ is $x$, such that every place $V'$ in the support of $D_0$ is fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$ and satisfies `P.IsStrictFst V'`, `P.IsStrictSnd V'`, or $P.\mathrm{reduceFst}\,V' \in W$. Assume an enumeration $idx : \mathrm{Fin}\,m \simeq \operatorname{supp} D_0$ together with $pos, neg : \mathrm{Fin}\,m \to \mathbb{N}$ presenting the coefficients, $D_0(idx\,j) = pos\,j - neg\,j$; assume that for each $j$ whose place is neither strict‑first nor strict‑second and reduces into $W$ one has $\mathrm{depth}(idx\,j) \le e(P.\mathrm{reduceFst}(idx\,j))$; and assume $v : \mathrm{Fin}\,m \to$ `X0MqComponents 𝔛reg.width` is given by the dictionary: strict‑first places go to `Sum.inl 1` if `swap` and to `Sum.inl 0` otherwise, strict‑second places to the other of these two, places reducing to $w \in W$ to `chainPos 𝔛reg.width (σN w) d` with $d$ the depth, respectively the width minus the depth when `swap`, and all remaining places to `Sum.inl 0`. The conclusion is that the function on `X0MqComponents 𝔛reg.width` obtained by evaluating $\sum_j \mathrm{single}(v\,j)\,(pos\,j - neg\,j)$, that is, the multidegree collecting the coefficients of $D_0$ according to the component each place is sent to, lies in the range of the additive endomorphism `intersectionAlpha` of $\mathbb{Z}$‑valued functions attached to the table `x0MqResolvedTable 𝔛reg.width`, whose multiplicities are all $1$ and whose intersection numbers are the adjacency values of the resolved two‑branch configuration corrected on the diagonal by minus the row sum, $c \mapsto \bigl(j \mapsto \sum_i c(i)\,\mathrm{inter}(i,j)\bigr)$.
--
--   This is the arithmetic half of the dictionary between divisors on the generic fibre and multidegrees on the special fibre of the resolved model of $X_0(p)$: triviality of Raynaud's component class forces the depth‑read multidegree to be a vertical one, i.e. to lie in the image of the intersection form of the resolved special fibre table. It is used by [`ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective`](thm.html#ModularCurve.DRModelPackage.exists_schemeHomOver_of_comp_eq_zero_of_abelJacobiPin_of_surjective) to produce a section over the base from a class with vanishing component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_multidegree_mem_range_intersectionAlpha_of_comp_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
open Classical in

theorem ModularCurve.DRResolvedModelPackage.multidegree_mem_range_intersectionAlpha_of_comp_eq_zero
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (e : Place k (modularFunctionFieldC k 1) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) → ℕ)
    (comp : ↥(inertiaInvariants A (1 * p)) →+ componentGroup (widthOfPlaces (arithFrobC p k 1) W e))
    (hlaw : P.DepthCompLaw (arithFrobC p k 1) W e depth comp)

    (O : Type) [CommRing O] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1)))
    (swap : Bool)

    (x : ↥(inertiaInvariants A (1 * p))) (hx : comp x = 0)
    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * p)))))
    (hD₀ : Pic0.mk D₀ = (x : JZero (1 * p)))
    (hadm : ∀ V' ∈ (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V' = V') ∧
        (P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ P.reduceFst V' ∈ W))
    (m : ℕ) (pos neg : Fin m → ℕ)
    (idx : Fin m ≃ ↥((D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))).support))
    (hcoef : ∀ j, ((pos j : ℤ) - (neg j : ℤ)) =
      (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)))
        (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))

    (hdepth : ∀ j, ¬ P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
        ¬ P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) →
        ∀ hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ∈ W,
          depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ≤
            e (P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))))

    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hdict : ∀ j, v j =
        (if P.IsStrictFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) then (if swap then Sum.inl 1 else Sum.inl 0)
         else if P.IsStrictSnd (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) then (if swap then Sum.inl 0 else Sum.inl 1)
         else if hw : P.reduceFst (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) ∈ W then
           DRResolvedModelPackage.chainPos 𝔛reg.width (σN ⟨_, hw⟩)
             (if swap then 𝔛reg.width (σN ⟨_, hw⟩) - depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
              else depth (idx j : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
         else Sum.inl 0)) :
    (fun w : X0MqComponents 𝔛reg.width => (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) w) ∈
      (MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)).range := by sorry
