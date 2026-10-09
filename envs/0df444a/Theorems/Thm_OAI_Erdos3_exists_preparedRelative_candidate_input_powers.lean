-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_preparedRelative_candidate_input_powers
-- name    : OAI.Erdos3.exists_preparedRelative_candidate_input_powers
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T09:23:15.883868+00:00
-- url     : https://prove2.me/theorems/b28171c4-2aec-457c-bb4a-aa78adefe770
-- title:
--   Base and precision powers dominating the prepared relative candidate inputs
-- statement:
--   Let $s$, $r$ (`relativePower`), $e$ (`childExponent`), $a$ (`normalizationPower`) and $g$ (`regularityPower`) be natural numbers. Then there exist natural numbers $b$ (`basePower`) and $c$ (`precisionPower`) with $2\le b$ and $2\le c$ such that for all real numbers $p$ and $v$ (`vars`) with $0\le p$, $0\le v$ and $v\le(p+2)^r$, writing $p_{\mathrm{rel}}=(p+2)^r$, $C=(p_{\mathrm{rel}}+4)^e$ (`childCost`), $N=(C+v+4)^a$ (`normBudget`) and $B=(p+2)^b$ (`Bstruct`), the following all hold: $N\le B$; $(N+2)^g\le B$; $p+16+(s+1)C+N\le B$; $C+1\le B$; $6p_{\mathrm{rel}}+35\le B$; and $3p_{\mathrm{rel}}+130\le(p+2)^c$.
--
--   Lean: `OAI.Erdos3.exists_preparedRelative_candidate_input_powers` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeInitializerScalarInputs.lean#L136

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

theorem exists_preparedRelative_candidate_input_powers
    (s relativePower childExponent normalizationPower regularityPower : ℕ) :
    ∃ basePower precisionPower : ℕ, 2 ≤ basePower ∧ 2 ≤ precisionPower ∧
    ∀ {p vars : ℝ}, 0 ≤ p → 0 ≤ vars → vars ≤ (p + 2) ^ relativePower →
      let pRelative := (p + 2) ^ relativePower
      let childCost := (pRelative + 4) ^ childExponent
      let normBudget := (childCost + vars + 4) ^ normalizationPower
      let Bstruct := (p + 2) ^ basePower
      normBudget ≤ Bstruct ∧ (normBudget + 2) ^ regularityPower ≤ Bstruct ∧
        p + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ Bstruct ∧
        childCost + 1 ≤ Bstruct ∧ 6 * pRelative + 35 ≤ Bstruct ∧
        3 * pRelative + 130 ≤ (p + 2) ^ precisionPower := by
  sorry

end Erdos3
end
end OAI
