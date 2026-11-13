-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_RationalStep_shortcut_correct_explicit
-- name    : OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct_explicit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:06:37.098706+00:00
-- url     : https://prove2.me/theorems/85145f75-cf55-478c-9303-34803e418103
-- title:
--   Shortcut extraction is correct for every r ≥ 2^2048 (explicit-cutoff form of OpenAI's lemma)
-- statement:
--   This is OpenAI's lemma `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct` (intermediate lemma of OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), restated with an explicit cutoff. Same namespace, same `open`s, same bundles, and the same conclusion word for word. The only change is the quantifier prefix: the published lemma begins "there is $R \ge 64^{16}$ such that for every $r \ge R$". This one begins "for every natural number $r \ge 2^{2048}$". Note that $2^{2048} \ge 64^{16}$.
--
--   So, for every $r \ge 2^{2048}$ and every multigraph $H$ on $n \ge 2$ vertices that packs $r$ edge-disjoint spanning trees, the state $a$ = `extractState H r` satisfies all of the following:
--   - its real matrix lies in OpenAI's `metricDomain H`;
--   - its active edges pack $q$ = `packingTarget` spanning trees, with $0 < q \le r$ and $(1 - 6r^{-1/16})\,r \le q$;
--   - every active edge has effective resistance at most $r^{-1/4}$ with respect to that matrix.
--
--   Why it exists: the constant of OpenAI's strong-thin-tree algorithm is proportional to this cutoff, and OpenAI proves only that one exists. The proof is OpenAI's, using `uniform_search_response_explicit`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (Apache License 2.0), explicit-cutoff form (r ≥ 2^2048) of OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT005
import Definitions.Def_OAIQ241TT006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

theorem shortcut_correct_explicit : ∀r : ℕ, 2^2048 ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      let a := extractState H r
      a.realMatrix ∈ metricDomain H ∧ H.TreePackable a.active a.packingTarget ∧
      0 < a.packingTarget ∧ a.packingTarget ≤ r ∧
      (1-6*(r:ℝ)^(-1/16:ℝ))*r ≤ (a.packingTarget:ℝ) ∧
      ∀e ∈ a.active, resistance H a.realMatrix e ≤ (r:ℝ)^(-1/4:ℝ) := by
  sorry

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end
