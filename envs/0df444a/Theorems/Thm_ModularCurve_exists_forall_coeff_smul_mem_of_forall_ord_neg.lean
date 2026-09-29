-- Prove2me | Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
-- name    : ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/8683487c-8baf-577d-93c8-caba9c3ab3b9
-- title:
--   Integral q-expansion from A-integral j-values at poles
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb Q}$ (the chosen algebraic closure of $\mathbb Q$) and a positive integer $N$. Let $f$ be a nonzero element of `modularFunctionFieldBar N`, the intermediate field of the Laurent series field $\overline{\mathbb Q}(\!(\mathfrak q)\!)$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of the elements of `modularFunctionFieldFull N`, the subfield of $\mathbb Q(\!(\mathfrak q)\!)$ generated over $\mathbb Q$ by the divisor expansions of level $N$; thus elements of this field are themselves Laurent series in $\mathfrak q$. Write $j$ for the element of this field given by the coefficientwise image of $\mathfrak q^{-1}$ times the power series $j$-numerator over $\mathbb Q$. Assume that at every pole of $f$ the function $j$ takes an $A$-integral value, in the following sense: for every place $W$ of `modularFunctionFieldBar N` over $\overline{\mathbb Q}$ — a valuation subring containing $\overline{\mathbb Q}$, distinct from the whole field, and a principal ideal ring, with $\operatorname{ord}_W$ the associated normalised additive valuation — such that $\operatorname{ord}_W f < 0$, there exists $a \in A$ with $\operatorname{ord}_W (j - a) > 0$. The conclusion is that some single nonzero scalar clears all denominators of the $\mathfrak q$-expansion of $f$: there is $c \in \overline{\mathbb Q}$, $c \neq 0$, such that for every integer $k$ the $k$-th Laurent coefficient of $c \cdot f$ lies in $A$.
--
--   This is the integrality half of a $\mathfrak q$-expansion principle for the function field of $X_0(N)$ over $\overline{\mathbb Q}$: control of $j$ at the poles of $f$ (no pole at the cusps, and none in the region where $j$ fails to be $A$-integral) forces the $\mathfrak q$-expansion of $f$ to be integral up to one scalar. It is used in the construction of integral models and residue data attached to specialisations of places, where functions in Riemann–Roch spaces of effective divisors with suitable support are reduced modulo the maximal ideal of $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (f : modularFunctionFieldBar N) (hf : f ≠ 0)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), W.ord f < 0 →
      ∃ a : A, 0 < W.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      ∀ k : ℤ, (c • (f : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A := by sorry
