-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/bc5a0459-2221-5a9f-86eb-02f10c7e641e
-- title:
--   Moving divisor classes off places outside the supersingular locus
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime not dividing $N$, and let $A$ be a valuation subring of a fixed algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ lying over $q$, in the sense that the image of $q$ lies in the non-units of $A$; then its residue field $\kappa$ has characteristic $q$. Fix: a finite set $W$ of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\ \kappa\ N$ consisting exactly of the supersingular places (rational places $w$ at which both $j$- and $j_N$-generators are regular and whose value of the $j$-generator lies in $\mathrm{ssJSet}\ q\ \kappa$); a modular polynomial datum $\mathrm{data}$ for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ killing the pair of $q$-expansions) satisfying the Kronecker congruence $\Phi\equiv (C X^{q}-X)(C X-X^{q})\bmod q$; integrality $h\alpha$, $h\beta$ of the two degeneracy embeddings $\bar\alpha,\bar\beta$ from level $N$ to level $Nq$; a place-specialization datum $P$ for $(A,q,N,\mathrm{data})$ with reduction map $\mathrm{residue}\ A$, which in particular produces two reductions $P.\mathrm{reduceFst}\,V$, $P.\mathrm{reduceSnd}\,V$ in the level-$N$ function field over $\kappa$ of each place $V$ of $\mathrm{modularFunctionFieldBar}(Nq)$; and a prolongation tuple $R$ for $P$ which is a model ($\mathrm{DivisorLawFst}$, $\mathrm{DivisorLawSnd}$, $\mathrm{CuspLawInfty}$, $\mathrm{CuspLawZero}$) and satisfies $R.\mathrm{RegularityLaw}\ W$ and $R.\mathrm{OrderLawFixed}$. Assume the moving engine: for every finite set $T$ of places of the level-$N$ function field over $\kappa$ there are divisors $E_0,C_0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ with $E_0,C_0$ effective, $E_0$ good for $P$ (each place in its support is strict for the first or for the second reduction, in the sense of the Frobenius relations $\mathrm{IsStrictFst}$/$\mathrm{IsStrictSnd}$), both reductions of every place in $\mathrm{supp}(E_0)$ outside $T$, $\deg E_0>0$, $\deg C_0>0$, $C_0$ fixed by $\mathrm{arithmeticGalois}$ applied to every element of the inertia subgroup of $A$ over $\mathbb Q$, and $E_0-C_0$ principal. The conclusion: for every finite set $T$ of places of $\mathrm{modularFunctionFieldC}\ \kappa\ N$ disjoint from $W$ and every class $x$ in $\mathrm{JZero}(Nq)=\mathrm{Pic}^0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$, there is a degree-zero divisor $E$ whose class is $x$ and such that $P.\mathrm{reduceFst}\,V\notin T$ and $P.\mathrm{reduceSnd}\,V\notin T$ for every $V$ in the support of $E$.
--
--   This is the moving step in the analysis of divisor classes on the level-$Nq$ modular curve along its reduction at $q$: a class is represented by a divisor whose support reduces away from a prescribed finite set of places of the special fibre, the set being required only to avoid the supersingular places. It feeds the construction of good representatives used in [`ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_rep_reduce_notMem_of_moving_of_disjoint_of_isModel
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
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed),
        (∀ T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)),
          ∃ E₀ C₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
            (∀ V, 0 ≤ E₀ V) ∧ P.IsGoodDiv E₀ ∧
              (∀ V ∈ E₀.support, P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T) ∧
                0 < Divisor.degree E₀ ∧ (∀ V, 0 ≤ C₀ V) ∧
                  (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                    arithmeticGalois (modularFunctionFieldFull (N * q)) σ • C₀ = C₀) ∧
                    0 < Divisor.degree C₀ ∧ Divisor.IsPrincipal (E₀ - C₀)) →
          ∀ (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))),
          (∀ w ∈ T, w ∉ W) →
          ∀ x : JZero (N * q),
            ∃ (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                  (F := ↥(modularFunctionFieldBar (N * q))))),
              Pic0.mk E = x ∧
                ∀ V ∈ (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
                  P.reduceFst V ∉ T ∧ P.reduceSnd V ∉ T := by sorry
