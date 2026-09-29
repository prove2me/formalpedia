-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_self_good_admissible
-- name    : ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_self_good_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/70cd8b64-8d22-59f5-bc25-cc44ffd7acf6
-- title:
--   Good admissible representatives stable under the q-correspondence
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, i.e. with $q$ a non-unit of $A$, so that its residue field $k=\mathrm{ResidueField}\,A$ has characteristic $q$. Fix a finite set $W$ of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in $\mathrm{ssJSet}\,q\,k$), a `ModularPolynomialData` $q$ datum $\Phi$ satisfying the Kronecker congruence $\Phi \bmod q = (C(X)^q-X)(C(X)-X^q)$, integrality of the two degeneracy embeddings $\overline{\mathcal F}_N\to\overline{\mathcal F}_{Nq}$ at level $N$ (hypotheses $h\alpha,h\beta$) and at level $Nq$ (hypotheses $h\alpha_q,h\beta_q$), a place specialisation $P$ over $A$ at $q$ with residue map $\mathrm{residue}\,A$, and assume principal divisors exist on $\mathrm{modularFunctionFieldBar}\,(Nq\cdot q)$. Put $S=\mathrm{nodePairsOfPlaces}$ of $W$ under the arithmetic Frobenius semilinear automorphism, the set of pairs $(w,\mathrm{Frob}\cdot w)$ for $w\in W$. Then for every class $x$ in $\mathrm{JZero}\,(Nq)$ that is $P$-good for $S$ — that is, $x=\mathrm{Pic0.mk}\,D$ for some degree-zero divisor $D$ all of whose support places are strict of first or second kind and whose glue datum lies in $\mathrm{GluingData.admissible}\,S$ — there is such a degree-zero representative $D$ for which, in addition, the divisorial Hecke correspondence $\mathrm{heckeDivBar}\,h\alpha_q\,h\beta_q\,D$ is again good and has admissible glue datum. No relation between the strict-kind parts of the translate and the translates of the strict-kind parts is asserted.
--
--   This is the member at $\ell=q$ of the family of moving lemmas for $P$-good admissible representatives of classes in the Jacobian at level $Nq$, the case in which the Hecke correspondence is the one attached to the prime of bad reduction; it is weaker in shape than its companions at $\ell\neq q$, asserting only preservation of goodness and admissibility. It feeds the computation of the component map on Hecke-algebra translates used in the analysis of the special fibre at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_self_good_admissible.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_self_good_admissible
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
      (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
      (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) q)
      [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * q))],
        (∀ (x : JZero (N * q)),
          P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) x →
            ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))),
              P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D
                ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ∧
              Pic0.mk D = x ∧
              P.IsGoodDiv (heckeDivBar hαq hβq
                (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) ∧
              P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (heckeDivBar hαq hβq
                    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)) := by sorry
