-- Prove2me | Theorems.Thm_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos
-- name    : ModularCurve.forall_ord_jBar_sub_le_zero_or_exists_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/d083ec55-15b9-52b8-80aa-c89edc46cb9a
-- title:
--   Pole-or-finite chart dichotomy for places of the modular function field
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $N$ be a nonzero natural number, and let $dataN$ be a level-$N$ modular polynomial datum, i.e. a monic $\Phi \in (\mathbb{Z}[X])[Y]$ of degree $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$ in $Y$ with $\Phi$ vanishing when $Y$ is specialised to the $q$-expansion $j_N$ and the coefficients are evaluated at $j$. Let $v$ be a place of the field $\overline{\mathbb{Q}}$-generated inside $\overline{\mathbb{Q}}((q))$ by the coefficientwise image of the full level-$N$ modular function field, that is, a proper valuation subring of that field containing $\overline{\mathbb{Q}}$ and which is a principal ideal ring; $\operatorname{ord}_v$ denotes minus the logarithm of the associated adic valuation. Write $j$ for the Laurent series $q^{-1}\,j\mathrm{Num}$ pushed into $\overline{\mathbb{Q}}((q))$ and $j_N$ for its image under the substitution $q \mapsto q^N$, both viewed as elements of that field. Then either $\operatorname{ord}_v(j - a) \le 0$ for every $a \in A$, or there are $a, a_N \in A$ with $\operatorname{ord}_v(j - a) > 0$ and $\operatorname{ord}_v(j_N - a_N) > 0$.
--
--   This is the valuation-theoretic case split underlying the specialisation of points of the modular curve: a place of the base-changed modular function field either sits over a pole of $j$ relative to $A$, or both coordinates $j$ and $j_N$ specialise to elements of $A$ at it, the second lying in $A$ because it is integral over $A$ via the modular equation. It is used in the analysis of places of the characteristic-$p$ fibre models and in the construction of place specialisations compatible with inertia, and it cites the fact that every place of the base-changed level-$M$ modular function field has degree one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos.lean

import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.forall_ord_jBar_sub_le_zero_or_exists_ord_pos
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (dataN : ModularPolynomialData N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (∀ a : A,
      v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) ∨
    ∃ a aN : A,
      0 < v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ∧
      0 < v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (aN : AlgebraicClosure ℚ)) := by sorry
