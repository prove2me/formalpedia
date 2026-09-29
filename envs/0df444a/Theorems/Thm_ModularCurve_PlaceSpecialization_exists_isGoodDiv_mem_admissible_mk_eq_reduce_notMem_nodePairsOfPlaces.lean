-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces
-- name    : ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7f23a201-8e95-5775-959b-4a2859365cf5
-- title:
--   Good representatives whose support avoids a finite set of places
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$; then the residue field $\kappa =$ `ResidueField A` has characteristic $q$. Let `data` be a modular polynomial datum at $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions) together with the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, and let $h\alpha$, $h\beta$ assert that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a place specialisation of $A$ at $q$ and level $N$ with target $\kappa$ and reduction the residue map of $A$, let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`, let $W$ be a finite set of places of `modularFunctionFieldC κ N` whose members are exactly the supersingular places `ssPlaces q N κ`, let $T$ be any finite set of places of that function field, and let $x$ be a class in $J_0 =$ `Pic0` of the level-$Nq$ field `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$. Write $S$ for the finite set of node pairs that $W$ determines under the arithmetic Frobenius semilinear automorphism `arithFrobC q κ N`. Then, assuming $x$ is a good class for $S$, there is a degree-zero divisor $D$ on the level-$Nq$ curve such that every place in the support of $D$ is strict on the first or on the second branch of $P$, the gluing datum `P.glueData S D` is admissible for $S$, the class of $D$ is $x$, and for every $V$ in the support of $D$ both reductions `P.reduceFst V` and `P.reduceSnd V` lie outside $T$.
--
--   This is the moving lemma for good classes on the level-$Nq$ modular curve: a good class is represented by a good, admissibly glued degree-zero divisor whose support reduces, along both degeneracy branches, away from a prescribed finite set of places. It is used in the construction of the glued specialisation comparing the two levels along the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
      (x : JZero (N * q)),
      P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) x →
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
            P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D ∈
                GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
              Pic0.mk D = x ∧
              ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by sorry
