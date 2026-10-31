-- Prove2me | Theorems.Thm_MultiServerAppt_wait_block_restriction
-- name    : MultiServerAppt.wait_block_restriction
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:02:28.114281+00:00
-- url     : https://prove2.me/theorems/0d2cd241-9f75-4a8a-afb7-28b8c0c6d5e4
-- title:
--   Eqs. (14), (16) — the waiting block (corrected: $S^{(1)}=S$)
-- statement:
--   The restriction of $p^{(s+i)}(t)$ to the saturated states equals
--
--   $$p_{\mathrm{wait}}^{(s+i)}(t)=\alpha_i^{\mathrm{wait}}\exp\big(S_i^{\mathrm{wait}}t\big).$$
--
--   The saturated states receive no flow from the unsaturated ones, so they evolve on their own.
--
--   Differences from the source:
--   - correction: printed start of the recursion S^(1) = 1 (p.12) → S^(1) = S, through Sblock; reason: the printed value is false: at s = 1, S = (-1), α = (1) it gives F_M(t) = 1 - e^t < 0
--   - generalization: (α, S) a phase-type law and t ≥ 0 → all matrices, all vectors and all real t; reason: this is a matrix identity for block triangular matrices; the source's case is an instance
--   - encoding: states (j, m) and matrices ordered in blocks by j descending → a sum type of saturated and unsaturated states, indexed by i with N = s + i; reason: a Lean convention; block order does not matter to a function of states
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (14), (16) and following display, pp.13-14

import Mathlib
import Definitions.Def_MultiServerAppt_pVec
import Definitions.Def_MultiServerAppt_waitMat
import Definitions.Def_MultiServerAppt_waitAlpha

open Matrix

namespace MultiServerAppt

/-- Eqs. (14), (16): the restriction of `p^(s+i)(t)` to the saturated states is
`p_wait^(s+i)(t) = α_i^wait exp(S_i^wait t)`. Kuiper–Lee, Appointment Scheduling for Multiple Servers,
SSRN 3975471, Eqs. (14), (16) and following display, pp.13-14.

**Formalization Note** A matrix identity for block upper triangular matrices. It needs no hypothesis
on `α`, `S`, `x`, or `t`. -/
theorem wait_block_restriction {ι : Type*} [Fintype ι] [DecidableEq ι] (s i : ℕ) (α : ι → ℝ)
    (S : Matrix ι ι ℝ) (x : ℕ → ℝ) (t : ℝ) :
    (fun p : SatState ι s i => pVec α S s x i t (.inl p)) =
      waitAlpha α S s x i ᵥ* NormedSpace.exp (t • waitMat α S s i) := by sorry

end MultiServerAppt
