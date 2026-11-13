-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_RationalStep_uniform_search_response_explicit
-- name    : OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response_explicit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:06:37.548791+00:00
-- url     : https://prove2.me/theorems/9418b5e7-fd9c-4065-8163-00a23564fb92
-- title:
--   Uniform search response for every r ≥ 2^2048 (explicit-cutoff form of OpenAI's lemma)
-- statement:
--   This is OpenAI's lemma `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response` (intermediate lemma of OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), restated with an explicit cutoff. Same namespace, same `open`s, same bundles, and the same conclusion word for word. The only change is the quantifier prefix: the published lemma begins "there is $r_0 \ge 8$ such that for every $r \ge r_0$". This one begins "for every natural number $r \ge 2^{2048}$".
--
--   So, for every $r \ge 2^{2048}$, every connected multigraph $H$ on $n \ge 2$ vertices with $m \ge r$ edges, and all rational data satisfying OpenAI's hypotheses, the rational search point `rational (search H s (target m r Q g) u)` lies in OpenAI's step-feasible region for the reduced target $Q - 2gr\beta_m$. The data are:
--   - capacities $0 \le u_e \le 1$;
--   - a scale $0 < s \le r^{1/4}$ and a quality $3r/4 \le Q \le r$;
--   - a gain $r^{-1/8} \le g \le 2r^{-1/8}$ with $gr \ge 3$;
--   - nonnegative slacks at baseline $\kappa_m$.
--
--   Here $\beta_m$ is `continuationStep m` and $\kappa_m$ is `continuationBaseline m`.
--
--   Why it exists: the constant of OpenAI's strong-thin-tree algorithm is proportional to the cutoff in this chain of lemmas, and OpenAI proves only that a cutoff exists. The proof is OpenAI's, using `finite_chain_response_explicit` and an explicit check of the numeric inequalities $10\,r^{-1/3} \le 1$ and $32\,r^{-1/3} \le r^{-1/8}$.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (Apache License 2.0), explicit-cutoff form (r ≥ 2^2048) of OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009

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

theorem uniform_search_response_explicit :
    ∀r : ℕ, 2^2048 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ → r ≤ m →
      ∀(u : Fin m → ℚ), (∀e, 0 ≤ (u e:ℝ)) → (∀e, (u e:ℝ) ≤ 1) →
      ∀(s Q g : ℚ), 0 < (s:ℝ) → (s:ℝ) ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ (Q:ℝ) → (Q:ℝ) ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ (g:ℝ) → (g:ℝ) ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      3 ≤ (g:ℝ)*r →
      (∀p, 0 ≤ slack H.left H.right (fun e => (u e:ℝ)+continuationBaseline m) (Q:ℝ) p) →
      (rational (search H s (target m r Q g) u)).real ∈
        stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
          ((Q:ℝ)-2*(g:ℝ)*r*continuationStep m) (fun e => (u e:ℝ)) := by
  sorry

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end
