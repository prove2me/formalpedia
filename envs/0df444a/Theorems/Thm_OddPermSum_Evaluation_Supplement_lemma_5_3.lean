-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_Supplement_lemma_5_3
-- name    : OddPermSum.Evaluation.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:41:46.364359+00:00
-- url     : https://prove2.me/theorems/3737532a-8f58-43fc-b829-dbf01fdadafc
-- title:
--   Lemma 5.3 (used in the proof of Theorem 1.2) — Truncated-ring value, inverse, determinant and gradient
-- statement:
--   Fix an admissible bilinear exponent $2<\omega\le3$. For every characteristic-two coefficient field $F$, one deterministic algebraic program, chosen before the dimensions and input matrix, takes the $L+1$ coefficients of each entry of $A\in R_L^{s\times s}$, where $s\ge1$ and $A(0)$ is invertible. It returns all four quantities
--   $$A^{-1},\quad\det A,\quad\Phi(A),\quad G(A).$$
--   There are $C>0$ and $k\in\mathbb N$, independent of $F,s,L,A$, for which the actual charged field-operation count is at most
--   $$C s^\omega(L+1)\bigl(\log_2(s+L+2)\bigr)^k.$$
--   The program receives $s,L$ as integer parameters. This supplies complete truncated-ring computation from a prime-field bilinear multiplier, without an oracle for ring operations.
--
--   Differences from the source:
--   - reading: a fixed admissible matrix multiplication exponent, with a bilinear algorithm used on p. 14 → UniformBilinearExponent with prime-field coefficients and an effective uniform circuit generator; reason: the changing finite fields require one uniform algorithm and the bilinear polynomial identity must lift to the truncated algebra; this is the structured brief’s prescribed reading
--   - encoding: soft-O field-operation complexity → one program and positive constants C,k preceding s,L and all matrix inputs, with an explicit logarithmic bound; reason: expands soft-O uniformly without a loss in the exponent or dependence on the truncation precision
--   - generalization: the finite coefficient field chosen in section 5 → every characteristic-two coefficient field, with C and k uniform over that field; reason: the ring algorithms on pp. 14–15 and 21 use characteristic two and uniform scalar polynomial arithmetic; the chosen finite field is a special case
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 14, Lemma 5.3

import Definitions.Def_OddPermSum_Evaluation_Supplement_bilinearMultiplier
import Definitions.Def_OddPermSum_Evaluation_Supplement_ringAlgorithmInterfaces

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

theorem lemma_5_3 (ω : ℝ) (hω : UniformBilinearExponent ω) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (F : Type) [Field F] [CharP F 2], ∃ p : AlgebraicProgram F,
    ∀ (s L : ℕ), 1 ≤ s → ∀ A : Matrix (Fin s) (Fin s) (Trunc F L),
      IsUnit (constantMatrix A).det → ∃ (fuel : ℕ) (st : MachineState F),
        runParameters p s L 0 (truncMatrixEncoding A) fuel = some st ∧
        st.outputs = allRingOutputs A ∧
        (st.cost : ℝ) ≤ C * (s : ℝ)^ω * (L+1) * (Real.logb 2 (s+L+2))^k := by sorry

end OddPermSum.Evaluation.Supplement
