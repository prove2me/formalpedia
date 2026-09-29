-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict
-- name    : ModularCurve.PlaceSpecialization.isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/4b72fae4-080a-5327-9d6a-b87d65701a24
-- title:
--   Inertial displacements of strict divisors: goodness and vanishing glue datum
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that the image of $q$ lies among the non-units of $A$; its residue field $\kappa = \mathrm{ResidueField}\,A$ then has characteristic $q$. Let $W$ be a finite set of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\,\kappa\,N$ whose members are exactly the supersingular places in the sense of `ssPlaces q N`, i.e. those places that are rational, are affine geometric places, and whose value at $\mathrm{jGeomGen}$ lies in $\mathrm{ssJSet}\,q$. Let `data` be modular polynomial data for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions of $j$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, let the two degeneracy maps $\overline{\alpha}, \overline{\beta}\colon \mathrm{laurentBaseChange}\,\overline{\mathbb{Q}}\,(\mathrm{modularFunctionFieldFull}\,N) \to \mathrm{laurentBaseChange}\,\overline{\mathbb{Q}}\,(\mathrm{modularFunctionFieldFull}\,(Nq))$ be integral ($h\alpha$, $h\beta$), and let $P$ be a place-specialisation datum over $A$ for these data with respect to the residue map $A \to \kappa$. For every $\sigma$ in $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$, the image in $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the inertia subgroup of $A$ inside its decomposition subgroup, and every divisor $E$ on the level-$Nq$ function field $\mathrm{modularFunctionFieldBar}\,(Nq)$ over $\overline{\mathbb{Q}}$ (a finitely supported $\mathbb{Z}$-valued function on places), the assertion is this: if every place $V$ in the support of $E$ satisfies $P.\mathrm{IsStrictFst}\,V$ (Frobenius on level-$N$ places over $\kappa$ carries $P.\mathrm{reduceFst}\,V$ to $P.\mathrm{reduceSnd}\,V$, while its square does not fix $P.\mathrm{reduceFst}\,V$) or $P.\mathrm{IsStrictSnd}\,V$ (the mirrored condition with the roles of the two reductions exchanged), then the divisor $D = \sigma \cdot E - E$, with $\sigma$ acting through $\mathrm{arithmeticGalois}$ at level $Nq$, again has all its support points strict of one of the two kinds, i.e. $P.\mathrm{IsGoodDiv}\,D$ holds, and its glue datum $P.\mathrm{glueData}$ at the node pairs $(w, \mathrm{arithFrobC}\,q\,\kappa\,N \cdot w)$ for $w \in W$ vanishes; the latter says that the pushforward of the first-kind part of $D$ along $P.\mathrm{reduceFst}$ and the pushforward of the second-kind part along $P.\mathrm{reduceSnd}$ are both the zero divisor.
--
--   This is the strict case of the specialisation of an inertial displacement $\sigma E - E$ on the level-$Nq$ modular curve: Galois equivariance of the two degeneracy maps forces inertia to fix both reductions of every place, so strictness is preserved and the pushed-down strict parts of $\sigma E$ and $E$ cancel. It feeds the constructions of good representatives with vanishing glued $\mathrm{Pic}^0$-pair for $\sigma x - x$, and thence the statement that such classes lie in the inertia invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.isGoodDiv_and_glueData_smul_sub_self_eq_zero_of_forall_isStrict
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          (∀ V ∈ E.support, P.IsStrictFst V ∨ P.IsStrictSnd V) →
            P.IsGoodDiv (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • E - E) = 0 := by sorry
