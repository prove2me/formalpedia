-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_Partitions_finite_chain_response_explicit
-- name    : OAI.AlgorithmicThinTrees.Partitions.finite_chain_response_explicit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:06:14.361208+00:00
-- url     : https://prove2.me/theorems/f10c833a-0a28-4cff-9278-12d9e9a00042
-- title:
--   Finite chain response for every r ≥ 2^2048 (explicit-cutoff form of OpenAI's lemma)
-- statement:
--   This is OpenAI's lemma `OAI.AlgorithmicThinTrees.Partitions.finite_chain_response` (intermediate lemma of OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), restated with an explicit cutoff. Same namespace, same `open`s, same bundles, and the same conclusion word for word. The only change is the quantifier prefix: the published lemma begins "there is $r_0 \ge 2$ such that for every $r \ge r_0$". This one begins "for every natural number $r \ge 2^{2048}$".
--
--   So, for every $r \ge 2^{2048}$, every connected multigraph $H$ on $n \ge 2$ vertices, every edge set $F$ and every finite chain $J$ of partitions such that:
--   - every part of every partition in $J$ is $\lfloor r/2\rfloor$-edge-connected in $H$ restricted to $F$,
--   - the whole vertex set is $\lfloor r/2\rfloor$-edge-connected in $H$ restricted to $F$,
--
--   and for every $0 < s \le r^{1/4}$, there is a centered positive matrix $Y$ in OpenAI's `metricDomain H` such that, for each partition $p \in J$, at most an $r^{-1/3}$ fraction of the edges of $F$ crossing $p$ fail $6s\, b_e b_e^{\mathsf T} \le Y$, where $b_e$ is the incidence vector of $e$.
--
--   Why it exists: the constant of OpenAI's strong-thin-tree algorithm is proportional to the cutoff in this chain of lemmas, and OpenAI proves only that a cutoff exists. The proof is OpenAI's, using `polynomial_nuclear_bound_explicit` at $\lfloor r/2\rfloor \ge 2^{2000}$ and an explicit check of the two numeric inequalities OpenAI derived from limits.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (Apache License 2.0), explicit-cutoff form (r ≥ 2^2048) of OAI.AlgorithmicThinTrees.Partitions.finite_chain_response

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

open MetricTests

theorem finite_chain_response_explicit :
    ∀r : ℕ, 2^2048 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ →
      ∀(F : Finset (Fin m)) (J : Finset (Setoid (Fin n))),
      IsChain (· ≤ ·) (J : Set (Setoid (Fin n))) →
      (∀p ∈ J, ∀A ∈ parts p, (H.restrict F).EdgeConnectedReal A (r/2:ℕ)) →
      (H.restrict F).EdgeConnectedReal univ (r/2:ℕ) →
      ∀s : ℝ, 0 < s → s ≤ (r:ℝ)^(1/4:ℝ) →
      ∃Y ∈ metricDomain H, CenteredPositive Y ∧ ∀p ∈ J,
        (((crossing H p ∩ F).filter (fun e =>
          ¬ (6*s) • vecMulVec (H.incidence e) (H.incidence e) ≤ Y)).card:ℝ) ≤
          (r:ℝ)^(-1/3:ℝ)*(crossing H p ∩ F).card := by
  sorry

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end
