-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2X_neg_one_lt
-- name    : OAI.InternalCatalan.barrierCase2X_neg_one_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:52.970613+00:00
-- url     : https://prove2.me/theorems/8f45cfd3-5440-4525-844b-1a8b0f5104e0
-- title:
--   OpenAI Catalan, Table 2 and Eq. (98) — X₂(−1) < −0.98399
-- statement:
--   Let $X_2$ be the case-$\kappa=2$ barrier function of the paper's Eq. (91) (`barrierCase2X`). Then
--
--   $$X_2(-1)<-0.98399 .$$
--
--   This is the row of Table 2 for $X_2$ at the finite division point $x=-1$ (type P, upper bound $-0.986727371546$), with the cutoff of Eq. (98). The value is an infinite series of complex logarithms, certified by rational arithmetic with explicit truncation errors (§7.3).
--
--   OpenAI, p. 41: “All finite division points have been included in Table 2: $-1$ for $X_2$; $1/4,1/2,3/4$ for $Y_2$; and $-1,-1/2,1/2$ for $X_1$.”
--
--   **Formalization note.** At $x=-1$ the term $\frac{19}{48}\log|x|$ vanishes and $\log(1-x)=\log2$. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 39-41, Table 2 (κ = 2, X, x = -1) and Eq. (98)

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem barrierCase2X_neg_one_lt : barrierCase2X (-1) < (-98399 / 100000 : ℝ) := by
  sorry

end OAI.InternalCatalan
