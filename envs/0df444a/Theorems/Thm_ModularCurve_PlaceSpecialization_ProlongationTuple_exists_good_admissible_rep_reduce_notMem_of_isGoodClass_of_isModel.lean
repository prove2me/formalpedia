-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/1582383c-e8bf-5e5d-91f2-bf0ca3d69935
-- title:
--   Moving good classes off a finite set of reductions
-- statement:
--   Let $N \geq 1$ and let $q$ be a prime not dividing $N$, let $A$ be a valuation subring of $\overline{\mathbf Q}$ with $q$ a non-unit of $A$ (so that its residue field $\kappa =$ `ResidueField A` has characteristic $q$), and let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ \kappa\ N$ whose members are exactly the supersingular places, i.e. the places that are rational, affine for the pair of generators $j, j_N$, and whose $j$-value lies in `ssJSet q κ`. Let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbf Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j^{(q)})$) satisfying the Kronecker congruence $\Phi \equiv (C X^q - X)(C X - X^q) \bmod q$, let the two level-raising maps $\mathrm{heckeAlphaBar}, \mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbf Q}$ be integral, let $P$ be a place specialisation of $A$ at $q$ in level $N$ with target $\kappa$ and reduction the residue map of $A$, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law at $W$, the node value law at $W$, and the order law at the $\varphi^2$-fixed affine places. Write $S = \mathrm{nodePairsOfPlaces}$ for the finite set of pairs $(w, \mathrm{arithFrobC}\ q\ \kappa\ N \cdot w)$ with $w \in W$. Then for every finite set $T$ of places of $\mathrm{modularFunctionFieldC}\ \kappa\ N$ and every $x \in \mathrm{Pic}^0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbf Q}$ which is a good class for $S$ (that is, $x$ is the class of some degree-zero divisor that is good and whose glue datum lies in the admissible subgroup for $S$), there is a degree-zero divisor $D$ of $\mathrm{modularFunctionFieldBar}(Nq)$ such that every place in the support of $D$ is strict on the first or on the second side, the glue datum $(\mathrm{reduceFst}_*(D|_{\text{strict fst}}), \mathrm{reduceSnd}_*(D|_{\text{strict snd}}), 0)$ is admissible for $S$ (both divisors of degree zero, the first vanishing at $s_1$ and the second at $s_2$ for each $s \in S$), the class of $D$ is $x$, and moreover $\mathrm{reduceFst}\ V \notin T$ and $\mathrm{reduceSnd}\ V \notin T$ for every $V$ in the support of $D$.
--
--   This is the moving lemma for the group of good divisor classes on the level-$Nq$ curve: a good class admissible at the node pairs over the supersingular places admits a representative whose two level-$N$ reductions avoid any prescribed finite set of places, the control over zeros of level-$Nq$ functions being supplied by the prolongation tuple and its laws rather than by the place specialisation alone. It is used by the statements that produce good admissible representatives compatible with the Hecke divisor and with prescribed avoidance of node pairs, in the comparison of the Jacobian of $X_0(Nq)$ with its specialisation in characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_good_admissible_rep_reduce_notMem_of_isGoodClass_of_isModel
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : P.ProlongationTuple) (_ : R.IsModel) (_ : R.RegularityLaw W)
      (_ : R.NodeValueLaw W) (_ : R.OrderLawFixed),
        ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
          (x : JZero (N * q)),
            P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) x →
              ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q)))),
                P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
                P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D
                  ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
                Pic0.mk D = x ∧
                ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by sorry
