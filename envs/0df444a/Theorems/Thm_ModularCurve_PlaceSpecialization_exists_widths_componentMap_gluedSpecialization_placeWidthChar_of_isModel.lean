-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_widths_componentMap_gluedSpecialization_placeWidthChar_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_widths_componentMap_gluedSpecialization_placeWidthChar_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ea5ec156-0bf6-5b70-b3ce-f8dedc40cf7e
-- title:
--   Widths, component map and glued specialisation over a place above q
-- statement:
--   Let $N$ be a positive integer and $q$ a prime not dividing $N$, let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ with $q$ a non-unit of $A$, so that the residue field $\kappa = \kappa(A)$ has characteristic $q$, and write $F_N =$ `modularFunctionFieldC` $\kappa$ $N$ for the field generated over $\kappa$ by the $q$-expansions $j$ and $j_N$, with $J_0(M)$ denoting `JZero` $M$, the degree-zero divisor class group of the base-changed modular function field of level $M$ over $\overline{\mathbb{Q}}$. Fix a finite set $W$ of places of $F_N$ whose members are exactly the supersingular places `ssPlaces q N κ`, and assume the finite set $\Sigma =$ `nodePairsOfPlaces (arithFrobC q κ N) W` of node pairs attached to $W$ and to the coefficientwise $q$-power Frobenius semilinear automorphism of $F_N$ is stable under that automorphism, in the sense that $(g\cdot s_1, g\cdot s_2)\in\Sigma$ for all $s\in\Sigma$. Fix further: a modular polynomial datum `data` for $q$ (a monic $\Phi$ of degree $\psi(q)$ in $\mathbb{Z}[X][Y]$ killing $(j,j_q)$) together with a witness that its reduction modulo $q$ is $(Y^q-X)(Y-X^q)$; integrality of the two degeneracy embeddings $\alpha,\beta$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$; a place specialisation $P$ of these data to $\kappa$ along the residue map of $A$; and a prolongation tuple $R$ for $P$ satisfying `IsModel` (the divisor laws at both legs and the cusp laws at $\infty$ and at $0$), `OrderLawFixed`, and the regularity and node-value laws for $W$. Then there exist a width function $e$ on the places of $F_N$ and additive maps $\mathrm{comp}$ and $\mathrm{sp}$ from the inertia invariants $J_0(Nq)^{I_A}$ (the classes fixed by the inertia subgroup of $A$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$) to, respectively, the component group of the width data $s\mapsto e(s_1)$ on $\Sigma$ (the $\mathbb{Z}$-dual of the character lattice modulo the image of the Gram map of the width pairing) and the glued degree-zero class group `GluedPic0` $\kappa$ $F_N$ $\Sigma$, such that: $e(w)>0$ for $w\in W$; $\mathrm{comp}$ is surjective; $\mathrm{comp}(x)=0$ holds exactly when $x$ is a good class for $P$ and $\Sigma$, that is the class of a degree-zero divisor supported at places strict for the first or the second leg whose glue datum is admissible; $\mathrm{sp}$ is a glued specialisation, that is it sends the class of any such good degree-zero divisor $D$ lying in the inertia invariants to the class of any admissible gluing datum equal to $P$'s glue datum of $D$; and $e(w) =$ `placeWidthChar q N w` for all $w\in W$, the characteristic-$q$ width $\,$ of $w$, namely the corrected $j$-width at $w.\mathrm{evalAt}(j)$ divided by the ramification index of $j$ at $w$.
--
--   This is the geometric input to level lowering at $q$: it packages the component group of the special fibre of $J_0(Nq)$ at a place above $q$, the Deligne–Rapoport description of that fibre as two copies of the level-$N$ curve glued along supersingular points, and the pinning of the crossing widths to the explicit characteristic-$q$ place widths. It is used by the statements that combine the component map with the Hecke action and the correspondence, and by the existence results producing a place specialisation together with its prolongation tuple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_widths_componentMap_gluedSpecialization_placeWidthChar_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_widths_componentMap_gluedSpecialization_placeWidthChar_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (hreg : R.RegularityLaw W) (hnv : R.NodeValueLaw W),
      ∃ (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
        (comp : ↥(inertiaInvariants A (N * q)) →+
          componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
        (sp : ↥(inertiaInvariants A (N * q)) →+
          GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
            (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
        (∀ w ∈ W, 0 < e w) ∧
        Function.Surjective comp ∧
        (∀ x : ↥(inertiaInvariants A (N * q)),
          comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q))) ∧
        P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp ∧
        (∀ w ∈ W, e w = placeWidthChar q N w) := by sorry
