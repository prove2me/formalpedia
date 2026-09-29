-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces_of_not_genusFF_pos
-- name    : ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces_of_not_genusFF_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/69c245fa-c874-58e5-a900-f0d27d5773fb
-- title:
--   Moving good classes off finite place sets: genus-zero case
-- statement:
--   Let $N \neq 0$ and let $q$ be a prime with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, so that its residue field $\kappa =$ `ResidueField A` has characteristic $q$. Fix a modular polynomial datum `data` at $q$ satisfying the Kronecker congruence (its bivariate reduction mod $q$ equals $(C X^q - X)(C X - X^q)$), integrality hypotheses $h\alpha, h\beta$ for the two degeneracy maps from level $N$ to level $Nq$ on base-changed Laurent-series function fields, a place specialization $P$ over $\kappa$ along the residue map, and a prolongation tuple $R$ of $P$ satisfying the four model laws (`IsModel`) and `OrderLawFixed`. Let $W$ be a finite set of places of `modularFunctionFieldC` $\kappa\,N$ whose members are exactly the supersingular places `ssPlaces q N` $\kappa$, let $T$ be any finite set of such places, and write $S$ for `nodePairsOfPlaces` of $W$ under the coefficient Frobenius `arithFrobC`. Then for every class $x \in$ `JZero` $(Nq)$ that is a good class for $S$ there is a degree-zero divisor $D$ on `modularFunctionFieldBar` $(Nq)$ with `IsGoodDiv` $D$, with `glueData` $S\,D$ admissible, with $\mathrm{Pic}^0$-class equal to $x$, and with $P.\mathrm{reduceFst}\,V \notin T$ and $P.\mathrm{reduceSnd}\,V \notin T$ for every $V$ in the support of $D$.
--
--   This is the genus-zero instance of the statement that good classes on the special fibre at $q$ of the modular curve of level $Nq$ admit good admissible representatives whose support avoids, on both branches, a prescribed finite set of places of the level-$N$ curve; such a choice of representative is what makes the component-group computation behind level lowering available. It feeds the general statement [`ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces`](thm.html#ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces_of_not_genusFF_pos.lean

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
open IsLocalRing ModularCurve
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_isGoodDiv_mem_admissible_mk_eq_reduce_notMem_nodePairsOfPlaces_of_not_genusFF_pos
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
      (hN : N ≠ 1)
      (hgenus : ¬ (0 < genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)))
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
