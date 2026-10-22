-- Prove2me | Theorems.Thm_FullFormalization_H_sub_H_pred
-- name    : FullFormalization.H_sub_H_pred
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:30:48.606293+00:00
-- url     : https://prove2.me/theorems/9768d1fe-0995-4405-a02f-edc9529c8f42
-- title:
--   Telescoping identity (5.1) in successor-index form
-- statement:
--   For every $N$ and every $k \in \mathbb{N}$, the prefix sums of the weight sequence satisfy
--
--   $$H_N(k+1) - H_N(k) = h_N(k+1), \qquad h_j = \frac{j+2}{2} - \frac{j(j+1)(j+2)}{2(N+1)(N+2)},$$
--
--   where $h_j$ is the cumulative gradient weight (4.3) and $H_j$ its partial sums (4.4). This is (5.1) written with successor indices, which sidesteps the truncated subtraction $j-1$; it is the recursion that turns $H$ into a genuine prefix sum of $h$.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §5, eq. (5.1) (equivalently §4.2, eq. (4.5)); Lean: FullFormalization.CoefficientIdentities lines 48-55

-- Generated from F:/20261008/FullFormalization\FullFormalization\CoefficientIdentities.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.CoefficientIdentities

  Source: section 5, Lemma 5.1, of
  `auditable_full_proof_nag_and_five_algorithm_cn.md`.

    (5.1)  H_j - H_{j-1} = h_j
    (5.2)  H_{N-1} = d_N
    (5.3)  h_j = 1 + m_j h_{j+1}            (source index range j < N-1)
    (5.4)  h_{N-1} = 1 + m_{N-1}
    (5.5)  D_j - D_{j+1} = (j+3)/4          (j >= 1)
    (5.6)  D_{j+2} = D_{j+1} - 1 - m_j (D_j - D_{j+1})     (j >= 1)

  Every one of these is a *symbolic* identity in `N` and the running index.
  There is no finite enumeration and no numerical substitution anywhere: the
  index appears as a universally quantified natural number and the proofs are
  rational-function identities closed by `field_simp`/`ring`.

  Index convention.  Statements that in the source use `j - 1` are phrased
  here in a positive-index form (with `j = k + 1`) so that the Lean statement
  carries no truncated natural-number subtraction; the literal `j - 1` form is
  recorded as a corollary in each case, so that the transcription to the source
  stays checkable.

  Lemma 5.1 in the source states (5.3) only for `j < N-1`, but the underlying
  rational-function identity is unconditional; the source's `j = N-1` instance
  is (5.4).  The unconditional form is recorded, and the source's restricted
  form follows by specialisation.  This strengthens an *intermediate* lemma
  only; no source theorem statement is altered.

  Also recorded here are the two `a`-side relations that the telescoping
  certificate uses, (10.6) and its companion, which follow from (5.1) by
  clearing the denominators `D_j, D_{j+1}, D_{j+2}`.
-/

import Mathlib
import Definitions.Def_Coefficients

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

/-! ### (5.1)  `H_j - H_{j-1} = h_j` -/





/-! ### (5.2)  `H_{N-1} = d_N` -/





/-! ### (5.3)  `h_j = 1 + m_j h_{j+1}` -/



/-! ### (5.4)  `h_{N-1} = 1 + m_{N-1}` -/







/-! ### (5.5)  `D_j - D_{j+1} = (j+3)/4` -/





/-! ### (5.6)  `D_{j+2} = D_{j+1} - 1 - m_j (D_j - D_{j+1})` -/



/-! ### The `a`-side relations of the telescoping certificate

Source (10.6): `a_{j-1} D_j = a_j D_{j+1} - h_j`; companion (used at (10.9)):
`a_{j+1} D_{j+2} = a_j D_{j+1} + h_{j+1}`. -/













end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

theorem FullFormalization.H_sub_H_pred (N k : ℕ) : H N (k + 1) - H N k = h N (k + 1) := by sorry
