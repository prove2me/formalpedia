-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2X_le_of_bracket_bounds
-- name    : OAI.InternalCatalan.barrierCase2X_le_of_bracket_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:38.960009+00:00
-- url     : https://prove2.me/theorems/e93f99c5-39db-44e2-b843-0125a6bf0173
-- title:
--   OpenAI Catalan, §7.2 and §7.4 — root exhaustion for X₂: a bound at x = −1 and on all eighteen root brackets bounds X₂ globally
-- statement:
--   Let $X_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2X`) and let $\mathcal M_X$ be the eighteen integers of the root table for $X_2$ on p. 38 (`barrierCase2XBrackets`). For every real $M$: if $X_2(-1)\le M$, and $X_2(x)\le M$ for every $m\in\mathcal M_X$ and every $x$ in the open bracket $\big(m/10^{10},(m+2)/10^{10}\big)$, then
--
--   $$X_2(x)\le M\qquad\text{for all }x\in[-1,0)\cup(0,1).$$
--
--   This is the root-exhaustion half of the certificate for $\sup X_2$: the derivative numerator $A_X$ of Eq. (93) has exactly one root in each listed bracket (a sign change at the ends, Eq. (95)) and no others in the open division intervals (the sign-variation counts of Eq. (94), by Descartes' rule of signs), and $X_2\to-\infty$ at the singular endpoints $0^\pm$ and $1^-$, so the supremum is attained at $x=-1$ or inside a bracket.
--
--   OpenAI, p. 41: “Every interior stationary point is in one of these brackets or is a division point. … The remaining endpoints are singular and have limit $-\infty$: $x\to0^\pm$ and $x\to1^-$ for $X_\kappa$ … Thus the root exhaustion, the finite endpoint values, and the derivative estimate together certify the global suprema, not merely the sampled values.”
--
--   **Formalization note.** The bracket for $m$ is $(m/10^{10},(m+2)/10^{10})$ (`barrierBracketLeft`, `barrierBracketRight`). Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 36-38, 41, §7.2 (Eq. (93)-(95)) and §7.4, root exhaustion for X_2

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan

open Set

theorem barrierCase2X_le_of_bracket_bounds (M : ℝ)
    (hneg : barrierCase2X (-1) ≤ M)
    (hbr : ∀ m ∈ barrierCase2XBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2X x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo (0 : ℝ) 1, barrierCase2X x ≤ M := by
  sorry

end OAI.InternalCatalan
