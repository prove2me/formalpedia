-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_reduceSnd_of_regularityLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/d8314cb8-cbb3-53a3-9428-d033f0fa94f6
-- title:
--   Common unit with a simple pole at V₀
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $N\ge 1$ with $q\nmid N$, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red}\colon A\to k$ a ring homomorphism; let `data` be modular polynomial data for $q$ whose bivariate reduction modulo $q$ satisfies the Kronecker congruence $(C X^{\,q}-X)(C X-X^{\,q})$, and assume the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ function field over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialisation for these data, and $R$ a prolongation tuple for $P$ — a pair of regular prolongations $R_1,R_2$ of $A$ to `modularFunctionFieldBar (N * q)` with values in the level-$N$ function field over the residue field of $A$, matched by the Atkin–Lehner involution — satisfying `R.IsModel` (the two divisor laws for the strict first and second reductions and the two cusp laws at the infinity- and zero-side places), the order law `R.OrderLawFixed` at Frobenius-fixed affine geometric places, and the regularity law `R.RegularityLaw W` for a finite set $W$ of places of `modularFunctionFieldC k N` which, by hypothesis, consists exactly of the supersingular places, that is, the rational affine geometric places at which $j$ takes a supersingular value. Let $V_0$ be a place of `modularFunctionFieldBar (N * q)` which is either of zero side for $P$ (cuspidal in the sense that $\mathrm{ord}_{V_0}(j_Q-a)\le 0$ for all $a\in A$, and $t_0=j/j_Q^{\,q}$ has at $V_0$ a value $\tau\in A$ with $\mathrm{red}\,\tau=1$) or strictly second (its first reduction is the Frobenius image of its second reduction, and the second reduction is not fixed by the square of Frobenius). Finally let $S$ be a finite subset of $k$ and $B$ a finite set of places of `modularFunctionFieldC k N`. Then there is $g$ in `modularFunctionFieldBar (N * q)`, lying in the integers of both $R_1$ and $R_2$, with both residues $R_1$-residue and $R_2$-residue of $g$ non-zero, with $\mathrm{ord}_{V_0}(g)=-1$, such that every place $V\ne V_0$ with $\mathrm{ord}_V(g)<0$ satisfies: there is $a\in A$ with $\mathrm{ord}_V(j-a)>0$ and $\mathrm{red}\,a\notin S$, and neither the first nor the second reduction of $V$ lies in $B$; and moreover the second residue of $g$ has order $-1$ at the second reduction of $V_0$.
--
--   This is the function-theoretic input for the two-component description of the reduction at $q$ of the curve of level $Nq$: a common unit for the two prolongations with a prescribed simple pole at a zero-side or strictly second place, whose remaining poles avoid a prescribed finite set of reductions and lie over $j$-values with residues outside a prescribed finite set, and whose second residue inherits the simple pole. It is used in the construction of representatives of divisor classes with support in general position, via [`ModularCurve.PlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces`](thm.html#ModularCurve.PlaceSpecialization.exists_rep_forall_exists_ord_sub_pos_residue_notMem_of_isModel_of_regularityLaw_of_orderLawFixed_of_ssPlaces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization.ProlongationTuple
open ModularCurve.PlaceSpecialization hiding jFun IsZeroSide

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_reduceSnd_of_regularityLaw
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (k : Type) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hRL : R.RegularityLaw W)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (hqN : ¬ q ∣ N)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV₀ : IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) (S : Finset k)
    (B : Finset (Place k (modularFunctionFieldC k N))) :
    ∃ (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∃ a : A, 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧ red a ∉ S) ∧
          P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
      (P.reduceSnd V₀).ord (R.residue₂ ⟨g, h₂⟩) = -1 := by sorry
