-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_bracket_left_lt
-- name    : OAI.InternalCatalan.barrierCase2Y_bracket_left_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:58.212739+00:00
-- url     : https://prove2.me/theorems/428d69c2-4e35-4d57-aeb7-a40ace3e0783
-- title:
--   OpenAI Catalan, Table 2 and Eq. (98) — Y₂ < −1.60890 at the left ends of all fifteen root brackets
-- statement:
--   Let $Y_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2Y`), built from the trial sequence $v$ of §7.1, and let $\mathcal M_Y$ be the fifteen integers of the root table for $Y_2$ on p. 38 (`barrierCase2YBrackets`): $176402802$, $330649406$, $764952882$, $1227250753$, $2149465998$, $3048189112$, $4322699096$, $5564757994$, $6801929373$, $8031988371$, $8877037851$, $9577761832$, $9838463999$, $9972727815$, $9992037196$. Then for every $m\in\mathcal M_Y$,
--
--   $$Y_2\big(m/10^{10}\big)<-1.60890 .$$
--
--   These are the fifteen bracket rows (type B) of Table 2 for $Y_2$, with the cutoff $-1.60890$ of Eq. (98). Each value is an infinite series of complex logarithms, certified by rational arithmetic with explicit truncation errors (§7.3).
--
--   OpenAI, p. 41: “With the $10^{-8}$ allowance, the weaker cutoffs we shall actually use are” $-.98399$ for $X$ and $-1.60890$ for $Y$ in case $\kappa=2$ (Eq. (98)).
--
--   **Formalization note.** The points are $m/10^{10}$ (`barrierBracketLeft m`, cast to $\mathbb R$). Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 38-41, Table 2 and Eq. (98), κ = 2, function Y

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem barrierCase2Y_bracket_left_lt (m : ℤ)
    (hm : m ∈ barrierCase2YBrackets) :
    barrierCase2Y (barrierBracketLeft m : ℝ) < (-160890 / 100000 : ℝ) := by
  sorry

end OAI.InternalCatalan
