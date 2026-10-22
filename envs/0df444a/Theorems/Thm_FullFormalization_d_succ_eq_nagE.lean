-- Prove2me | Theorems.Thm_FullFormalization_d_succ_eq_nagE
-- name    : FullFormalization.d_succ_eq_nagE
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:59:31.894532+00:00
-- url     : https://prove2.me/theorems/e838247b-dbdd-4e00-b544-45a4fa3bd274
-- title:
--   The $y$-sequence reconstructs $d$: $d_{k+1} = e_{k+1} + m_k(e_{k+1} - e_k)$
-- statement:
--   For every $k$, the rational-NAG coefficient sequence is recovered from the $y$-sequence $e_j$ of the run through the momentum formula
--   $$d_{k+1} = e_{k+1} + m_k\,(e_{k+1} - e_k),$$
--   where $e_0 = 0$, $e_{k+1} = d_k + 1$ is the scalar coordinate of the $y$-iterate, $m_k = k/(k+3)$ is the rational momentum, and $d_j = j(j+7)/8$ (4.1). This is source (3.2): the rational momentum turns the $y$-sequence back into the $d$-sequence of the NAG trajectory of §27.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §3, eq. (3.2); Lean: FullFormalization.CommonExtremizer lines 280-300

-- Generated from F:/20261008/FullFormalization\FullFormalization\CommonExtremizer.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.CommonExtremizer

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 27-31:
  the common extremizer that gives the lower bound of Theorem B.

  The setting is section 23: `L = 1`, `R = 1`, `x_init = 0`, and the ambient
  space is `EuclideanSpace ℝ (Fin D)` with `D = 2N+1`.  Section 24 produces the
  unit *hidden direction* `u` (first `N` coordinates zero, orthogonal to every
  predetermined random-search query), and sections 25-26 build the extremal
  function

      f_N(z) = H_c(⟪u,z⟫ - 1) + (1/2)‖z - ⟪u,z⟫ u‖²,   c = 1/(2 d_N + 1),

  which is convex, differentiable, globally 1-smooth, with unique minimiser `u`
  and `f_N(u) = 0` (`LiftedHuber.lean`).  This file runs the five strategies on
  that one function:

  * (27) the rational-NAG iterates are `x_k = d_k c u` for `k ≤ N`, all in the
    Huber linear region `⟪u,x_k⟫ = d_k c ≤ d_N c < 1 - c`, and
    `q_{NAG,N}(f_N) = 1/(2(2 d_N+1)) = tau_N` — the *upper* bound is attained;
  * (28) GD with step `1/L = 1` outputs `N c u`, and
    `q_{GD,N} - tau_N = (d_N - N)/(2 d_N+1)²  ≥ 0`; half-GD outputs `(Nc/2) u`
    with `q_{halfGD,N} - tau_N = (d_N - N/2)/(2 d_N+1)² ≥ 0`;
  * (29) every fixed-seed query lies in `u^⊥`, so `f_N(q_i) = B_N + ½‖q_i‖² ≥ B_N`;
    the output is one of the queries, so `q_{rand,N} ≥ B_N > tau_N`;
  * (30) every grid-then-refine query touches only the first `N` coordinates,
    hence lies in `u^⊥`; `f_N(z) = B_N + ½‖z‖²` there, so the origin stays the
    incumbent through both phases — the decision logic is *proved*, not assumed —
    and `q_{grid,N} = B_N > tau_N`;
  * (31) the minimum of the five losses is therefore exactly `tau_N`: the
    portfolio value coincides with the NAG value on this single function.

  Everything is proved for an arbitrary unit `u` with vanishing first `N`
  coordinates and an arbitrary orthogonal query list, so the construction is
  uniform in `u`; `exists_extremizer` then produces such a `u` from
  `HiddenDirection.exists_unit_hidden_direction`, and `theoremB_sup_eq_tau`
  turns the result into the `sup = tau_N` statement given the universal upper
  bound of section 22 as a hypothesis.

  Nothing is postulated: no `sorry`, `admit`, `axiom` or `unsafe`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_CommonExtremizer
import Definitions.Def_FunctionClass
import Definitions.Def_GradientStrategies
import Definitions.Def_GridRefine
import Definitions.Def_HiddenDirection
import Definitions.Def_LiftedHuber
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_RandomSearch
import Definitions.Def_RationalNAG
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_mom_eq
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagE_succ

open scoped Gradient RealInnerProductSpace Topology
open Set

set_option linter.unusedSectionVars false

namespace FullFormalization

noncomputable section

/-! ### Scalars: the cutoff `c = 1/(2 d_N+1)` and the value `B_N` -/





















/-! ### The value of `f_N` on vectors orthogonal to `u`

`LiftedHuber.liftedHuber_eq` gives `f_N(z) = H_c(⟪u,z⟫-1) + ½‖z - ⟪u,z⟫u‖²`;
on `u^⊥` the first term is the constant `H_c(-1) = c - c²/2 = B_N` (26.5)-(26.6)
and the second is `½‖z‖²`. -/







/-! ### The hidden direction and the first-coordinate support

`HiddenDirection.exists_unit_hidden_direction` supplies `u` with `‖u‖ = 1`,
`u j = 0` for every coordinate `j` with `j < N`, and `⟪u, q i⟫ = 0` for every
predetermined query.  Vectors whose coordinates `≥ N` vanish are exactly the
vectors of the source's "first `N` coordinate directions", and they are all
orthogonal to `u`. -/















/-! ### Section 27: the NAG trajectory on the extremizer -/

















/-! ### Section 28: the two gradient-descent strategies -/

























/-! ### Section 29: fixed-seed random search -/











/-! ### Section 30: grid-then-refine -/



























/-! ### Section 31: the five algorithms combined -/























end

end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace Topology
open Set
set_option linter.unusedSectionVars false

theorem FullFormalization.d_succ_eq_nagE (k : ℕ) :
    d (k + 1) = nagE (k + 1) + mom k * (nagE (k + 1) - nagE k) := by sorry
