-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_table_left_lt_3
-- name    : OAI.InternalCatalan.barrierCase2Y_table_left_lt_3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T20:46:37.50614+00:00
-- url     : https://prove2.me/theorems/88aeb61a-a0c3-4e30-9c62-453e0ec7856c
-- title:
--   OpenAI Catalan, Table 2 and Eq. (98) — Y₂ < −1.60890 at the left ends of root brackets 7–9
-- statement:
--   Let $Y_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2Y`), built from the trial sequence $v$ of §7.1, and let $m$ be any of the three integers $4322699096$, $5564757994$ and $6801929373$ (brackets 7–9 of the fifteen in the root table for $Y_2$ on p. 38). Then
--
--   $$Y_2\big(m/10^{10}\big)<-1.60890 .$$
--
--   These are bracket rows 7–9 (type B) of Table 2 for $Y_2$, with the cutoff $-1.60890$ of Eq. (98). Each value is an infinite series of complex logarithms, certified by rational arithmetic with explicit truncation errors (§7.3).
--
--   OpenAI, p. 41: “With the $10^{-8}$ allowance, the weaker cutoffs we shall actually use are” $-.98399$ for $X$ and $-1.60890$ for $Y$ in case $\kappa=2$ (Eq. (98)).
--
--   **Formalization note.** The split of the fifteen brackets into groups of three is not the paper's; it keeps each proof within the platform's time limit. The points are $m/10^{10}$ (`barrierBracketLeft m`, cast to $\mathbb R$). Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 38-41, Table 2 and Eq. (98), κ = 2, function Y, root brackets 7-9

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem barrierCase2Y_table_left_lt_3 :
    ∀ m ∈ ([4322699096, 5564757994, 6801929373] : List ℤ),
      barrierCase2Y (barrierBracketLeft m : ℝ) < (-160890 / 100000 : ℝ) := by
  sorry

end OAI.InternalCatalan
