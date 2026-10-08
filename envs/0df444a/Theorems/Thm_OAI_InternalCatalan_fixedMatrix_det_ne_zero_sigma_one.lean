-- Prove2me | Theorems.Thm_OAI_InternalCatalan_fixedMatrix_det_ne_zero_sigma_one
-- name    : OAI.InternalCatalan.fixedMatrix_det_ne_zero_sigma_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:41.709251+00:00
-- url     : https://prove2.me/theorems/7f4c4c6c-d304-4121-bcce-2e122c30a0f8
-- title:
--   OpenAI Catalan, Eq. (48) — the fixed 48×48 matrix 𝓑₀ + 𝓑₁ is nonsingular
-- statement:
--   Let $\mathcal B$ be the fixed rational $49\times48$ matrix of the paper's Eq. (47) (`fixedBaseEntryRat`), and let $\mathcal B_0=(\mathcal B(r,k))_{0\le r,k<48}$ and $\mathcal B_1=(\mathcal B(r+1,k))_{0\le r,k<48}$ (`fixedB0`, `fixedB1`; `fixedMatrix σ` is $\mathcal B_0+\sigma\mathcal B_1$). Then
--
--   $$\det(\mathcal B_0+\mathcal B_1)\ne0 .$$
--
--   This is the second of the three fixed assertions of Eq. (48), to which the nonvanishing of the large determinants $\Delta_p$ at prime scales (Proposition 4.1) is reduced.
--
--   OpenAI, p. 19: “The arithmetic certificate below proves $\det\mathcal B_0\ne0$, $\det(\mathcal B_0+\mathcal B_1)\ne0$, $\det(\mathcal B_0-\mathcal B_1)\ne0$. (48)”
--
--   **Formalization note.** The determinant is of a $48\times48$ matrix over $\mathbb Q$; the three assertions of Eq. (48) are published as three statements. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 19, 24, Eq. (48), det(B_0 + B_1) ≠ 0

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem fixedMatrix_det_ne_zero_sigma_one : (fixedMatrix 1).det ≠ 0 := by
  sorry

end OAI.InternalCatalan
