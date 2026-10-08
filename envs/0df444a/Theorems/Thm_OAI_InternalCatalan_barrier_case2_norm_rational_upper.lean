-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrier_case2_norm_rational_upper
-- name    : OAI.InternalCatalan.barrier_case2_norm_rational_upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T19:00:45.276286+00:00
-- url     : https://prove2.me/theorems/0888262f-fd11-429b-a0e2-a12b69416e39
-- title:
--   OpenAI Catalan, Eq. (98) — the norm term 2‖p‖²_* + ½‖v‖²_* is at most 0.77843 for the case-two trial sequences
-- statement:
--   Let $p,v$ be the case-$\kappa=2$ trial sequences of the paper's §7.1 (`barrierP2`, `barrierV2`), and for a real sequence $u$ let $\|u\|_*^2=\sum_{k\ge1}u_k^2/k$ (`barrierTrialNormSq`). Then
--
--   $$2\|p\|_*^2+\tfrac12\|v\|_*^2\le\frac{48651467}{62500000}=0.778423472 .$$
--
--   This is the norm entry of Eq. (98) for $\kappa=2$ (there rounded up to $.77844$): the series are evaluated in closed form through logarithms of $1-zz'$ for the exponential tails, and bounded by rational arithmetic.
--
--   OpenAI, p. 41, Eq. (98): “With the $10^{-8}$ allowance, the weaker cutoffs we shall actually use are” $\kappa\|p\|_*^2+\frac12\|v\|_*^2$: $.77844$ for $\kappa=2$.
--
--   **Formalization note.** The Lean constant $48651467/62500000$ is slightly sharper than the paper's $.77844$. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 40-41, Eq. (98), κ = 2, the norm term

import Mathlib
import Definitions.Def_OAICatalanIrrationality

namespace OAI.InternalCatalan


theorem barrier_case2_norm_rational_upper :
    2 * barrierTrialNormSq barrierP2 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV2 ≤
      (48651467 / 62500000 : ℝ) := by
  sorry

end OAI.InternalCatalan
