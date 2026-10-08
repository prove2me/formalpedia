-- Prove2me | Theorems.Thm_OAI_InternalCatalan_fixedLiteralModMinus_rightInverse_rows_0_23
-- name    : OAI.InternalCatalan.fixedLiteralModMinus_rightInverse_rows_0_23
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:01:17.391897+00:00
-- url     : https://prove2.me/theorems/d8b98736-f35a-40d9-a05a-5e97fce6fa80
-- title:
--   OpenAI Catalan, §4.4 — rows 0–23 of the right-inverse certificate for 𝓑₀ − 𝓑₁ modulo 101
-- statement:
--   Let $\bar{\mathcal B}_-$ be the explicit $48\times48$ matrix over $\mathbb F_{101}$ in the definitions bundle (`fixedLiteralModMinus`, the reduction of $D(\mathcal B_0-\mathcal B_1)$ modulo $101$), and let $J$ be the explicit $48\times48$ matrix over $\mathbb F_{101}$ (`fixedLiteralInvMinus`). For every row index $i$ with $0\le i\le 23$ and every column index $0\le k<48$,
--
--   $$(\bar{\mathcal B}_-\,J)_{ik}=\delta_{ik}\qquad\text{in }\mathbb F_{101}.$$
--
--   Together with rows $24$–$47$ this says $\bar{\mathcal B}_-J=I$, so $\bar{\mathcal B}_-$ is invertible over $\mathbb F_{101}$: the finite certificate behind $\det(\mathcal B_0-\mathcal B_1)\ne0$ in Eq. (48).
--
--   OpenAI, p. 24: “Every listed pivot is nonzero. Since the swaps and row additions are invertible, all three matrices are invertible modulo 101 and hence have nonzero determinants over $\mathbb Q$.”
--
--   **Formalization note.** The paper certifies invertibility by Gaussian elimination with the pivots of Table 1; OpenAI's Lean certificate is an explicit right inverse $J$, checked row by row. The split of the $48$ rows into two halves is not the paper's; it keeps each proof within the platform's resource limits. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 24, §4.4 and Eq. (48): invertibility of B_0 − B_1 modulo 101, rows 0-23

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem fixedLiteralModMinus_rightInverse_rows_0_23 (i : Fin 48)
    (hi : 0 ≤ i.val ∧ i.val < 24) (k : Fin 48) :
    (fixedLiteralModMinus * fixedLiteralInvMinus) i k = (1 : Matrix (Fin 48) (Fin 48) (ZMod 101)) i k := by
  sorry

end OAI.InternalCatalan
