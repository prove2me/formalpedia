-- Prove2me | Theorems.Thm_ModularCurve_exists_finset_forall_coeff_mem_valuationSubring
-- name    : ModularCurve.exists_finset_forall_coeff_mem_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/6973a402-fcd2-52ce-a88f-0caba179e189
-- title:
--   Almost all places are integral for finitely many q-expansions
-- statement:
--   Fix a natural number $N$, nonzero, and a natural number $r$, and let $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` be a family of $r$ elements of the intermediate field `modularFunctionFieldBar N` of $\overline{\mathbb Q}((q)) =$ `LaurentSeries (AlgebraicClosure ℚ)` over $\overline{\mathbb Q}$; by definition this field is `laurentBaseChange` of `modularFunctionFieldFull N`, that is the subfield generated over $\overline{\mathbb Q}$ by the image, under the coefficientwise embedding `coeffEmb` of $\mathbb Q((q))$ into $\overline{\mathbb Q}((q))$, of the field $F_N =$ `modularFunctionFieldFull N` obtained by adjoining to $\mathbb Q$ inside $\mathbb Q((q))$ the set of Laurent series `divisorExpansions N`. The assertion is that there exists a finite set $S$ of natural numbers, all of whose members are prime, with the following property: for every prime $\ell \notin S$, for every valuation subring $A$ of $\overline{\mathbb Q}$ such that `A.LiesOverPrime ℓ`, i.e. the image of $\ell$ in $\overline{\mathbb Q}$ lies in the nonunits of $A$, for every index $i$ and every integer $k$, the $k$-th coefficient of the Laurent series $s\,i$ belongs to $A$.
--
--   This is the bounded-denominators statement for $q$-expansions of modular functions on $X_0(N)$ over $\overline{\mathbb Q}$: finitely many such functions have coefficients integral at all places of $\overline{\mathbb Q}$ lying above all but finitely many rational primes. It is used by [`ModularCurve.exists_constantReduction_chartData_of_isEmbBasis`](thm.html#ModularCurve.exists_constantReduction_chartData_of_isEmbBasis) to produce chart data for the modular curve whose reduction is available at almost all residue characteristics.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finset_forall_coeff_mem_valuationSubring.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_finset_forall_coeff_mem_valuationSubring (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ (i : Fin r) (k : ℤ), ((s i : LaurentSeries (AlgebraicClosure ℚ)).coeff k) ∈ A := by sorry
