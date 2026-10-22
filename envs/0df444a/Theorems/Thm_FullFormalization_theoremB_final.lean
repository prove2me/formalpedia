-- Prove2me | Theorems.Thm_FullFormalization_theoremB_final
-- name    : FullFormalization.theoremB_final
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T08:48:34.318497+00:00
-- url     : https://prove2.me/theorems/20a6c533-69c8-460b-8b07-59a82ff913d7
-- title:
--   Theorem B: the exact five-algorithm worst-case constant
-- statement:
--   For every N >= 1, L > 0, R > 0, initial point x_init in GridSpace N, and predetermined query list q, the declared five-strategy portfolio has exact normalized worst-case value tau_N = 2/(N^2+7N+4). In particular, N=3 gives 1/17.
--
--   The universal upper-bound clause permits an output tuple out only when its NAG component is exactly nagX f L x_init N, as explicitly required in the Lean statement. Its loss is the minimum over the five Strategy entries. The lower-bound clause uses the concrete frozen portfolioOutputScaled and constructs an admissible scaled lifted-Huber function attaining tau_N simultaneously for that portfolio.
--
--   The domain in this statement has dimension 2N+1, and q is fixed before the function is chosen. The result concerns the specified five strategies. It is not a lower bound for all possible optimization algorithms.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21-§32, eq. (7.1), (30.2), (32.1); Lean: FullFormalization.MainResults lines 53-74

-- Generated from F:/20261008/FullFormalization\FullFormalization\MainResults.lean (Phase 3, minimal stub: no inlined
-- helper theorems — the statement does not need them).
/-
  FullFormalization.MainResults

  Assembles the two headline results of the source document from the files that
  prove their halves, with **no hypothesis left standing in for a theorem**.

    * Theorem A — `auditable_full_proof_nag_and_five_algorithm_cn.md`, §17-§20:
      `TheoremA.theorem_A_upper`, `TheoremA.theorem_A_sup`;
    * Theorem B — §21-§32: `TheoremB.theoremB`, which up to now carried
      `TheoremAUpper N (GridSpace N)` as an explicit hypothesis because
      `TheoremA.lean` did not yet exist.

  This file supplies that hypothesis from `TheoremA.theorem_A_upper` and
  restates Theorem B without it.  Nothing is weakened: `TheoremAUpper` was
  always exactly the statement of Theorem A in the vocabulary of the portfolio
  file, and `TheoremB.theoremB`'s own docstring says so.
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
import Definitions.Def_Huber1D
import Definitions.Def_LiftedHuber
import Definitions.Def_NAGUpperBound
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_Positivity
import Definitions.Def_RandomSearch
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Definitions.Def_TheoremA
import Definitions.Def_TheoremB
import Theorems.Thm_FullFormalization_theoremAUpper_of_theorem_A
import Theorems.Thm_FullFormalization_theoremB

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]







end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem FullFormalization.theoremB_final (N : ℕ) (hN : 1 ≤ N) (q : Fin N → GridSpace N)
    (L R : ℝ) (hL : 0 < L) (hR : 0 < R) (x_init : GridSpace N) :
    (∀ (f : GridSpace N → ℝ) (xstar : GridSpace N) (out : Strategy → GridSpace N),
        AdmissibleUnique L R f x_init xstar → out Strategy.nag = nagX f L x_init N →
        SNOf L R f (f xstar) out ≤ tau N) ∧
      (∃ u : GridSpace N, ‖u‖ = 1 ∧
        AdmissibleUnique L R (scaled L R x_init (liftedHuber u N)) x_init (x_init + R • u) ∧
        SNOf L R (scaled L R x_init (liftedHuber u N))
          ((scaled L R x_init (liftedHuber u N)) (x_init + R • u))
          (portfolioOutputScaled R x_init u q hN) = tau N) ∧
      tau N = 2 / ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4) := by sorry
