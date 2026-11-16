-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_lemma_6_3
-- name    : OddPermSum.Evaluation.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:44:36.919283+00:00
-- url     : https://prove2.me/theorems/73ab6455-3ad0-4a8b-821c-b66b110acec1
-- title:
--   Lemma 6.3 (used in the proof of Theorem 1.3) — Gradient-column and rank-one updates
-- statement:
--   Let $A\in R_L^{s\times s}$ be invertible, and suppose $B=A^{-1}$, $\Delta=\det A$ and $\varphi_A=\Phi(A)$ are given as input. For a row $\rho$ and index $i$, put $A'=A+e_i\rho$, $g=G(A)_{*,i}$, $b=Be_i$, $v=\rho B$, and $\eta=1+v_i$. Then
--   $$\Phi(A')=\Phi(A)+\rho g,\qquad\det A'=\Delta\eta.$$
--   If $\eta$ is a unit, then
--   $$(A')^{-1}=B+\eta^{-1}bv.$$
--   Moreover, $\rho(0)=0$ guarantees that $\eta$ is a unit. One program over each coefficient field, chosen before $s,L,A,B,\Delta,\varphi_A,i,\rho$, computes $g$, both updated scalars, and the updated inverse when applicable, using at most
--   $$C s^2(L+1)\bigl(\log_2(s+L+2)\bigr)^k$$
--   charged field operations, with $C>0$ and $k$ independent of all inputs and the coefficient field. This is a simultaneous query-and-update statement, including all algebraic clauses and the unit safeguard.
--
--   Differences from the source:
--   - encoding: soft-O field-operation complexity → one program and positive constants C,k preceding s,L and all matrix inputs, with an explicit logarithmic bound; reason: expands soft-O uniformly without a loss in the exponent or dependence on the truncation precision
--   - encoding: inverse of a unit and available stored quantities → Ring.inverse under IsUnit and explicit coefficient-list inputs for B, determinant and value; reason: ring inverse is only asserted valid for units and the input interface retains the source availability convention
--   - generalization: the finite coefficient field chosen in section 5 → every characteristic-two coefficient field, with C and k uniform over that field; reason: the ring algorithms on pp. 14–15 and 21 use characteristic two and uniform scalar polynomial arithmetic; the chosen finite field is a special case
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 20, Lemma 6.3

import Definitions.Def_OddPermSum_Evaluation_Supplement_ringAlgorithmInterfaces

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem lemma_6_3 :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (F : Type) [Field F] [CharP F 2], ∃ p : AlgebraicProgram F,
    ∀ (s L : ℕ) (A B : Matrix (Fin s) (Fin s) (Trunc F L))
      (δ φA : Trunc F L) (i : Fin s) (ρ : Fin s → Trunc F L),
      IsUnit A.det → B = A⁻¹ → δ = A.det → φA = phi A →
      phi (rowUpdate A i ρ) = phi A + ∑ j, ρ j * gradient A j i ∧
      (rowUpdate A i ρ).det = δ * updateEta B i ρ ∧
      (IsUnit (updateEta B i ρ) → (rowUpdate A i ρ)⁻¹ = inverseUpdate B i ρ) ∧
      ((∀ j, truncCoeff (ρ j) 0 = 0) → IsUnit (updateEta B i ρ)) ∧
      ∃ (fuel : ℕ) (st : MachineState F),
        runParameters p s L i.val (updateInputs A B δ φA ρ) fuel = some st ∧
        st.outputs = updateOutputs A i ρ ∧
        (st.cost : ℝ) ≤ C * (s : ℝ)^2 * (L+1) * (Real.logb 2 (s+L+2))^k := by sorry

end OddPermSum.Evaluation.Supplement
