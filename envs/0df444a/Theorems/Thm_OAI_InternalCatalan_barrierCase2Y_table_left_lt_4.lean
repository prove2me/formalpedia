-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2Y_table_left_lt_4
-- name    : OAI.InternalCatalan.barrierCase2Y_table_left_lt_4
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T20:44:55.886979+00:00
-- url     : https://prove2.me/theorems/40257926-149d-4fed-bb76-9ae2b4cf28f6
-- title:
--   OpenAI Catalan, Table 2 and Eq. (98) — Y₂ < −1.60890 at the left ends of root brackets 10–12
-- statement:
--   Let $Y_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2Y`), built from the trial sequence $v$ of §7.1, and let $m$ be any of the three integers $8031988371$, $8877037851$ and $9577761832$ (brackets 10–12 of the fifteen in the root table for $Y_2$ on p. 38). Then
--
--   $$Y_2\big(m/10^{10}\big)<-1.60890 .$$
--
--   These are bracket rows 10–12 (type B) of Table 2 for $Y_2$, with the cutoff $-1.60890$ of Eq. (98). Each value is an infinite series of complex logarithms, certified by rational arithmetic with explicit truncation errors (§7.3).
--
--   OpenAI, p. 41: “With the $10^{-8}$ allowance, the weaker cutoffs we shall actually use are” $-.98399$ for $X$ and $-1.60890$ for $Y$ in case $\kappa=2$ (Eq. (98)).
--
--   **Formalization note.** The split of the fifteen brackets into groups of three is not the paper's; it keeps each proof within the platform's time limit. The points are $m/10^{10}$ (`barrierBracketLeft m`, cast to $\mathbb R$). Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 38-41, Table 2 and Eq. (98), κ = 2, function Y, root brackets 10-12

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem barrierCase2Y_table_left_lt_4 :
    ∀ m ∈ ([8031988371, 8877037851, 9577761832] : List ℤ),
      barrierCase2Y (barrierBracketLeft m : ℝ) < (-160890 / 100000 : ℝ) := by
  sorry

end OAI.InternalCatalan
