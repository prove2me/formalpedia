-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_le_of_bracket_bounds
-- name    : OAI.InternalCatalan.barrierCase2Y_le_of_bracket_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:41.038536+00:00
-- url     : https://prove2.me/theorems/6a580729-56e3-460d-b63e-a0ea2cf4f1dd
-- title:
--   OpenAI Catalan, §7.2 and §7.4 — root exhaustion for Y₂: a bound on all fifteen root brackets bounds Y₂ on (0, 1)
-- statement:
--   Let $Y_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2Y`) and let $\mathcal M_Y$ be the fifteen integers of the root table for $Y_2$ on p. 38 (`barrierCase2YBrackets`). For every real $M$: if $Y_2(s)\le M$ for every $m\in\mathcal M_Y$ and every $s$ in the open bracket $\big(m/10^{10},(m+2)/10^{10}\big)$, then
--
--   $$Y_2(s)\le M\qquad\text{for all }s\in(0,1).$$
--
--   This is the root-exhaustion half of the certificate for $\sup Y_2$: the derivative numerator $A_Y$ of Eq. (93) has its roots in $(0,1)$ exactly in the listed brackets (sign changes at the ends, Eq. (95), and the sign-variation counts of Eq. (94)), and $Y_2\to-\infty$ at $0^+$ and $1^-$.
--
--   OpenAI, p. 41: “Every interior stationary point is in one of these brackets or is a division point. … The remaining endpoints are singular and have limit $-\infty$: … $x\to0^+$ and $x\to1^-$ for $Y_\kappa$.”
--
--   **Formalization note.** The hypothesis concerns only the brackets; no separate bound at the paper's division points $1/4,1/2,3/4$ is assumed. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 36-38, 41, §7.2 (Eq. (93)-(95)) and §7.4, root exhaustion for Y_2

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan

open Set

theorem barrierCase2Y_le_of_bracket_bounds (M : ℝ)
    (hbr : ∀ m ∈ barrierCase2YBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2Y x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, barrierCase2Y x ≤ M := by
  sorry

end OAI.InternalCatalan
