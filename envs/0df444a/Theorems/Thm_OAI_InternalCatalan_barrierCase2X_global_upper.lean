-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2X_global_upper
-- name    : OAI.InternalCatalan.barrierCase2X_global_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:42.397097+00:00
-- url     : https://prove2.me/theorems/97a70c37-4f39-40f0-aa3e-af726c716e4b
-- title:
--   OpenAI Catalan, §7.4 — the barrier function X₂ is at most −0.98399 + 0.000024 on [−1, 1) ∖ {0}
-- statement:
--   Let $X_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2X`). For every real $x$ with $-1\le x<1$ and $x\ne0$,
--
--   $$X_2(x)\le-0.98399+0.000024 .$$
--
--   This is the global supremum bound for $X_2$ used in Proposition 7.1: every interior stationary point of $X_2$ lies in one of the eighteen certified root brackets (an exact Descartes sign-variation count), the value at each bracket's left end is below $-0.98399$ (Table 2), a derivative bound moves it by less than $0.000024$ across a bracket, and the endpoint $x=-1$ is evaluated separately.
--
--   OpenAI, p. 41: “It follows from the mean value theorem that moving from a left bracket endpoint to its stationary point increases either value by less than $120000\cdot\frac{2}{10^{10}}=.000024$.” and “Thus the root exhaustion, the finite endpoint values, and the derivative estimate together certify the global suprema, not merely the sampled values.”
--
--   **Formalization note.** The domain $[-1,1)\setminus\{0\}$ is that of $X_\kappa$ in Eq. (91). Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 41, §7.4 (global supremum of X_2)

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem barrierCase2X_global_upper {x : ℝ}
    (hx : -1 ≤ x ∧ x < 1 ∧ x ≠ 0) :
    barrierCase2X x ≤ (-98399 / 100000 : ℝ) + 24 / 1000000 := by
  sorry

end OAI.InternalCatalan
