-- Prove2me | Theorems.Thm_InfoRelax_IdealPenalty_dual_value_fn_eq_value_fn
-- name    : InfoRelax.IdealPenalty.dual_value_fn_eq_value_fn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:26.133386+00:00
-- url     : https://prove2.me/theorems/21c026d7-45a9-4fb5-85a3-8dfc93ba6e5e
-- title:
--   §2.3 — with $w_t = V_{t+1}$ the dual value functions equal the primal ones, $V^{\mathbb G}_t = V_t$
-- statement:
--   Consider a recursive DP as in eq. (2) (natural filtration with $\mathcal F_0=\{\emptyset,\Omega\}$, countable action set, nonempty feasible sets, bounded $\mathcal F_t$-measurable period rewards). Let $\mathbb G$ be any relaxation of $\mathbb F$ and take the generating functions $w_t(a)=V_{t+1}(a_0,\dots,a_t)$ built from the primal value functions of (2). Then for every $t=0,\dots,T+1$ and every action sequence,
--   $$V^{\mathbb G}_t=V_t\quad\text{almost surely},$$
--   where $V^{\mathbb G}_t$ are the dual value functions of (10).
--
--   This identity is the core of Theorem 2.3: with the ideal generating functions the dual recursion reproduces the primal recursion, so the dual bound equals the primal value.
--
--   **Formalization Note** The equality is almost sure because conditional expectations are determined only almost everywhere. For $t>T+1$ both sides are $0$.
-- source:
--   Brown, Smith & Sun, Information Relaxations and Duality in Stochastic Dynamic Programs, Oper. Res. (Articles in Advance, 2010), DOI 10.1287/opre.1090.0796, p. 5, §2.3, the paragraph before Theorem 2.3

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework
import Definitions.Def_InfoRelax_IdealPenalty_RecursiveModel
import Definitions.Def_InfoRelax_IdealPenalty_Penalty

open MeasureTheory

namespace InfoRelax.IdealPenalty

/-- **§2.3, the induction before Theorem 2.3**, Brown, Smith & Sun (2010), Oper. Res., DOI
10.1287/opre.1090.0796, p. 5.

In the recursive setting, let `𝔾` be a relaxation of `𝔽` and take the generating functions
`w_t(a) = V_{t+1}(a_0, …, a_t)` from the primal value functions (2). Then the dual value functions
of (10) equal the primal value functions: `V^𝔾_t = V_t` for every `t = 0, …, T + 1` (and
trivially beyond), almost surely, for every action sequence.

**Formalization Note.** Equality is almost sure (`=ᵐ[μ]`) because conditional expectations are
determined only a.e. Pinned: countable action type with the discrete σ-algebra. -/
theorem dual_value_fn_eq_value_fn {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [DiscreteMeasurableSpace X] [Countable X] [DecidableEq X] {T : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : RecursiveDP Ω X T) (hM : M.Valid)
    (𝔾 : Filtration (Fin (T + 1)) mΩ) (h𝔾 : IsRelaxation M.𝔽 𝔾) :
    ∀ (t : ℕ) (a : Fin (T + 1) → X),
      dualValueFn M μ 𝔾 (idealGen M μ) t a =ᵐ[μ] valueFn M μ t a := by sorry

end InfoRelax.IdealPenalty
