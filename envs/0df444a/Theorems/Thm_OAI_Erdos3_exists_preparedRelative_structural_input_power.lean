-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_preparedRelative_structural_input_power
-- name    : OAI.Erdos3.exists_preparedRelative_structural_input_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:25:23.995384+00:00
-- url     : https://prove2.me/theorems/81c6d4fd-25e7-45b8-b787-9eae2b24fe94
-- title:
--   A relative power dominating the prepared relative structural inputs
-- statement:
--   Let $s$ be a natural number. Then there is a natural number $r$ (`relativePower`) with $2\le r$ such that for every real $p\ge2$ and all natural numbers $D$ and $n_X$ with $D\le p$ and $n_X\le p$, writing $M=$ `preparationCoordinateCap s D (s * D)` (where `preparationCoordinateCap s D T` $=D(T+1)^s+D+T+1$), $J=$ `modularInitialBlockCount s (nX + s * M)` (where `modularInitialBlockCount s d` $=2^s(\texttt{modularInitialRankStrength}\ s\ d+d+10)+1$ and `modularInitialRankStrength s d` $=2^{2s}s!(d+2)$), $\mathrm{dim}=$ `enlargedPreparedCommonSamplerDimension s M J` (a natural number given by an explicit formula in $s$, $M$, $J$ and the numbers `preparedCommonBlockCount s j`) and $p_{\mathrm{rel}}=(p+2)^r$, the following all hold: $p\le p_{\mathrm{rel}}$, $s+3\le p_{\mathrm{rel}}$, $M\le p_{\mathrm{rel}}$, $J\le p_{\mathrm{rel}}$, $\mathrm{dim}\le p_{\mathrm{rel}}$, and `allocatedUniformChartLog M` $+1\le p_{\mathrm{rel}}$, where `allocatedUniformChartLog x` $=20(x+1)^3$.
--
--   Lean: `OAI.Erdos3.exists_preparedRelative_structural_input_power` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean#L99

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {m s D nX : ℕ}

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

theorem exists_preparedRelative_structural_input_power (s : ℕ) :
    ∃ relativePower : ℕ, 2 ≤ relativePower ∧ ∀ {p : ℝ}, 2 ≤ p →
    ∀ D nX : ℕ, (D : ℝ) ≤ p → (nX : ℝ) ≤ p →
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      let pRelative := (p + 2) ^ relativePower
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative := by
  sorry

end Erdos3
end
end OAI
