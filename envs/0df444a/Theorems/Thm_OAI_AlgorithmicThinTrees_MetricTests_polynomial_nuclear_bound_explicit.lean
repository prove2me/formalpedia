-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_polynomial_nuclear_bound_explicit
-- name    : OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound_explicit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:06:15.169212+00:00
-- url     : https://prove2.me/theorems/d8fef124-131b-4a8a-8542-7e0eb4a02968
-- title:
--   Polynomial nuclear bound for every q ≥ 2^2000 (explicit-cutoff form of OpenAI's lemma)
-- statement:
--   This is OpenAI's lemma `OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound` (intermediate lemma of OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), restated with an explicit cutoff. Same namespace, same `open`s, same bundles, and the same conclusion word for word. The only change is the quantifier prefix: the published lemma begins "there is $q_H \ge 2$ such that for every $q \ge q_H$". This one begins "for every natural number $q \ge 2^{2000}$".
--
--   So, for every $q \ge 2^{2000}$, every multigraph $G$ on $n$ vertices, every hierarchy $H$ on which $G$ is locally $q$-edge-connected (in the real sense of `LocallyConnectedReal`), and every family $M$ of non-root hierarchy nodes whose parent boundary carries at least a $1/q$ fraction of the node's cut:
--   - for every centered test matrix $Z$ and every probability vector $\lambda$ on $M$,
--   - the squared trace of $\sqrt{\sqrt Z \, \Phi_\lambda \sqrt Z}$ is at most $\tfrac12 q^{-31/40}$ times $\operatorname{tr}(L_G Z)$,
--   - where $\Phi_\lambda$ is OpenAI's `ShortcutDual.objectiveMatrix` of the parent boundaries.
--
--   Why it exists: OpenAI's proof shows that its threshold exists, via limits, without bounding it. The constant of OpenAI's strong-thin-tree algorithm is proportional to the largest such threshold, so an explicit bound is what lets the algorithm's thinness constant be compared with a fixed number. The proof is OpenAI's, with the asymptotic step replaced by a direct verification of OpenAI's `GoodParameters` for every real $x \ge 2^{2000}$.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (Apache License 2.0), explicit-cutoff form (q ≥ 2^2000) of OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT006

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

theorem polynomial_nuclear_bound_explicit :
    ∀ q : ℕ, 2^2000 ≤ q →
      ∀ (n m : ℕ) (G : MultiGraph n m) (H : Hierarchy n),
      H.LocallyConnectedReal G q →
      ∀ M : Finset (Finset (Fin n)), M ⊆ H.nodes →
      (∀t ∈ M, t ≠ univ) →
      (∀t ∈ M, ((G.cut univ t).card : ℝ)/q ≤ (H.parentBoundary G t).card) →
      ∀ (Z : Matrix (Fin n) (Fin n) ℝ), Test Z →
      ∀ (lam : M → ℝ), (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix G.incidence
        (fun t : M => H.parentBoundary G t) lam*CFC.sqrt Z)).trace^2 ≤
        ((q:ℝ)^(-31/40:ℝ)/2)*(G.laplacian univ*Z).trace := by
  sorry

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end
