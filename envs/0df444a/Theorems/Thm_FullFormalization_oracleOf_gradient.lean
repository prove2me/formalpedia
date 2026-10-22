-- Prove2me | Theorems.Thm_FullFormalization_oracleOf_gradient
-- name    : FullFormalization.oracleOf_gradient
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:31:04.290628+00:00
-- url     : https://prove2.me/theorems/4d982b18-36e5-4821-b8ed-684d83d222e4
-- title:
--   The oracle of a function reports Mathlib's gradient
-- statement:
--   For every function $f : E \to \mathbb{R}$ on a real inner product space, the gradient field reported by the canonical oracle $\mathrm{oracleOf}(f)$ is definitionally Mathlib's gradient:
--
--   $$
--   (\mathrm{oracleOf}(f)).\mathrm{gradient} = \nabla f.
--   $$
--
--   The oracle is the single query interface each of the five strategies is written against: one call at a point $x$ returns both the value $f(x)$ and the gradient there, matching the frozen implementation's `query(point)`. Identifying its gradient component with $\nabla f$ is what makes the rational-NAG recursion — stated directly in terms of $\nabla f$ — literally the same loop as the audited implementation.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §21, the five-strategy problem and query interface (source lines 2057-2107); Lean: FullFormalization.PortfolioDefinitions lines 100-102

-- Generated from F:/20261008/FullFormalization\FullFormalization\PortfolioDefinitions.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.PortfolioDefinitions

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 21 and
  30 (Theorem B, the five-algorithm portfolio).

  Section 21 fixes the objects this file defines:

    * the upstream task publishes `L > 0`, `R > 0` and `x_init`;
    * the function class is the differentiable convex globally `L`-smooth
      class of `FunctionClass.lean` (`Admissible`, with the unique-minimizer
      refinement `AdmissibleUnique`, source line 2065);
    * the five strategies run in the **normalized coordinate**

          z = (x - x_init) / R            (source line 2074),

      namely (1) GD with step `1/L`, (2) GD with step `1/(2L)`,
      (3) rational-NAG, (4) fixed-seed random search, (5) grid-then-refine;
    * the per-strategy loss is

          q_{A,N}(f) = (f(x_{out,A}) - f*) / (L R^2)     (source line 2090),

      and the portfolio value is

          S_N(f) = min_A q_{A,N}(f)                       (source line 2096).

  Representation choices:

  * `Oracle` is the query interface every strategy is written against: one
    oracle call returns a value *and* a gradient, exactly as the frozen
    implementation's `oracle.query(point)` returns `{"value": ..,
    "gradient": ..}` (`blackbox_algos.py`, `_gd_fixed_1_over_L` et al.).  The
    canonical instance for a differentiable function `f` is `oracleOf f`, whose
    gradient field is Mathlib's `∇ f` (`oracleOf_gradient`, defeq); the
    definitional equality is what makes `RationalNAG.nagX` — which is written
    against `∇ f` — literally the frozen Nesterov loop.

  * `toNormalized` / `ofNormalized` are the two directions of the change of
    variables (source line 2074).  `R ≠ 0` is needed for the round trips; the
    source has `R > 0` (line 2062).

  * `Strategy` is the five-element enumeration required by
    `DEPENDENCY_MAP.md` §36.4 ("`PortfolioDefinitions.Strategy` 为五元 `Fin 5`
    枚举，无 `∀` 量词"): five constructors, in the source's order 1-5.  There is
    no quantifier over algorithms anywhere in the portfolio; `SN` is the
    minimum over exactly these five.

  * `SN` takes the vector of the five per-strategy losses `Strategy → ℝ`.  The
    losses themselves are produced by the concrete runs of
    `GradientStrategies.lean`, `RandomSearch.lean` and `GridRefine.lean` (and
    `RationalNAG.lean` for strategy 3); `SNOf` packages that wiring, so
    `SNOf L R f fstar out` *is* the source's `S_N(f)` for the five outputs
    `out : Strategy → E`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_PortfolioDefinitions

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*}

/-! ### The oracle -/



namespace Oracle







end Oracle

section OracleOf

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]







end OracleOf

/-! ### What a strategy run produces -/



/-! ### Normalized coordinates (source line 2074) -/

section Normalized

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]













end Normalized

/-! ### The loss of one strategy (source line 2090) -/

section Loss

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]







end Loss

/-! ### The five strategies and the portfolio minimum (source lines 2079-2096) -/















section Portfolio

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]









end Portfolio

end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
variable {E : Type*}
section OracleOf
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

@[simp] theorem FullFormalization.oracleOf_gradient (f : E → ℝ) : (oracleOf f).gradient = ∇ f := by sorry
