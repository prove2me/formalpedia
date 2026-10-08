-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_global_upper
-- name    : OAI.InternalCatalan.barrierCase2Y_global_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:57.292896+00:00
-- url     : https://prove2.me/theorems/dbe8f27a-f381-4302-9d24-c10b0350bda4
-- title:
--   OpenAI Catalan, §7.4 — the barrier function Y₂ is at most −1.60890 + 0.000024 on (0, 1)
-- statement:
--   Let $Y_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2Y`). For every real $s$ with $0<s<1$,
--
--   $$Y_2(s)\le-1.60890+0.000024 .$$
--
--   This is the global supremum bound for $Y_2$ used in Proposition 7.1: every interior stationary point of $Y_2$ lies in one of the fifteen certified root brackets or is one of the division points $1/4,1/2,3/4$, the values there are below $-1.60890$ (Table 2), and a derivative bound moves them by less than $0.000024$ across a bracket.
--
--   OpenAI, p. 41: “It follows from the mean value theorem that moving from a left bracket endpoint to its stationary point increases either value by less than $120000\cdot\frac{2}{10^{10}}=.000024$.” and “Thus the root exhaustion, the finite endpoint values, and the derivative estimate together certify the global suprema, not merely the sampled values.”
--
--   **Formalization note.** The domain $(0,1)$ is that of $Y_\kappa$ in Eq. (91). Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 41, §7.4 (global supremum of Y_2)

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem barrierCase2Y_global_upper {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    barrierCase2Y x ≤ (-160890 / 100000 : ℝ) + 24 / 1000000 := by
  sorry

end OAI.InternalCatalan
