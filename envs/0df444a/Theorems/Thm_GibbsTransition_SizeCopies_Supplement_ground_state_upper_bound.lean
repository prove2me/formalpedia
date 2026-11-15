-- Prove2me | Theorems.Thm_GibbsTransition_SizeCopies_Supplement_ground_state_upper_bound
-- name    : GibbsTransition.SizeCopies.Supplement.ground_state_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:43:59.664193+00:00
-- url     : https://prove2.me/theorems/cc395be6-2cb1-457b-bb40-e7339b5196d3
-- title:
--   Theorem A.2 — Ground-state upper bound
-- statement:
--   On every general field-coupled class, let $d=b-a$, $C=\max(1,3J+J_b)$, and take rational $0<\epsilon\le1/16$, $0<\delta\le1/4$. The specified Appendix A learner is correct and a universal positive constant $A$, fixed before all physical parameters, gives
--   $$\sup_u\mathbb E_u[V]\le\frac{AC^3}{d^5\epsilon^3}\log(1/\delta).$$
--   Its maximum side is $O(C/(d\epsilon))$, its queried fields have dyadic encodings with $O(\log(1/\epsilon))$ bits, and its complete copy bound is
--   $$N=O\!\left(d^{-2}\left[K\log(1/\delta)+K^2\right]\right),\quad K=\left\lceil\frac{\log(1/(4\epsilon))}{\log(8/5)}\right\rceil.$$
--   All constants are uniform in the local dimension, public physical parameters, accuracy, confidence and unknown interaction. The dyadic denominator is $2^{3K+2}$. The statement also certifies that the explicitly computed sample counts lie in the source intervals. The scheduled copy, size and spin counts hold on every comparison path and hence bound the expected costs.
--
--   The local operation is the POVM $\{P,I-P\}$ at a uniformly random site of each fresh normalized ground-space copy. No runtime assertion is added to the quoted theorem.
--
--   Differences from the source:
--   - encoding: big-O resources and expected supplied spins of the specified algorithm → uniform positive constants and deterministic schedule sums, with exact denominator 2^(3K+2); reason: each path has the same widths, sample counts and sizes, so the deterministic counts are the stated expected resources
--   - generalization: a boundary prescription with a uniform effective algebraic encoding → an algebraic Hermitian boundary prescription with a uniform computable rational Cauchy table; reason: an effective algebraic encoding supplies this table; the statements use only certified approximations and the same surface norm bound, so every source boundary is included without requiring uniform recovery of exact algebraic descriptions
-- source:
--   Yuhao Cai, Zhenzhang Li, STOC 2027 submission #1168 (October 2026), Theorem A.2, printed p. 22 (PDF p. 24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1168.pdf

import Mathlib
import Definitions.Def_GibbsTransition_SizeCopies_Supplement_GroundLearner
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false

namespace GibbsTransition.SizeCopies.Supplement

theorem ground_state_upper_bound :
    ∃ A Cs Cn Cb : ℝ, 0 < A ∧ 0 < Cs ∧ 0 < Cn ∧ 0 < Cb ∧
    ∀ (q : ℕ) (p : FieldData q), ValidField p →
    ∀ epsilon delta : ℚ, 0 < epsilon → epsilon ≤ 1/16 → 0 < delta → delta ≤ 1/4 →
    GroundLearns p epsilon delta ∧
    groundRounds epsilon = searchRounds epsilon ∧
    (groundSpins p epsilon delta : ℝ) ≤
      A*(surfaceC p : ℝ)^3 / ((gap p : ℝ)^5*(epsilon : ℝ)^3) * Real.log (1/(delta : ℝ)) ∧
    (groundCopies p epsilon delta : ℝ) ≤
      Cn*(gap p : ℝ)⁻¹^2 * ((groundRounds epsilon : ℝ)*Real.log (1/(delta : ℝ))+
        (groundRounds epsilon : ℝ)^2) ∧
    (3*(groundRounds epsilon : ℝ)+2 ≤ Cb*Real.log (1/(epsilon : ℝ))) ∧
    ∀ k < groundRounds epsilon,
      (groundSide p k : ℝ) ≤ Cs*(surfaceC p : ℝ)/((gap p : ℝ)*(epsilon : ℝ)) ∧
      (2 / ((gap p : ℝ)/4)^2 * Real.log (2/(roundFailure epsilon delta k : ℝ)) ≤
        (groundCount p epsilon delta k : ℝ)) ∧
      ((groundCount p epsilon delta k : ℝ) <
        2 / ((gap p : ℝ)/4)^2 * Real.log (2/(roundFailure epsilon delta k : ℝ))+2) ∧
      ∀ h : List Bool, h.length = k →
        ∃ m : ℕ, m ≤ 2^(3*groundRounds epsilon+2) ∧
          historyField h k = (m : ℚ)/2^(3*groundRounds epsilon+2) := by sorry

end GibbsTransition.SizeCopies.Supplement
