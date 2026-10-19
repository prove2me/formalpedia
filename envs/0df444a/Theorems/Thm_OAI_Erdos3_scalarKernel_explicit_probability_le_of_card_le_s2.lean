-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarKernel_explicit_probability_le_of_card_le_s2
-- name    : OAI.Erdos3.scalarKernel_explicit_probability_le_of_card_le_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:33:02.444111+00:00
-- url     : https://prove2.me/theorems/84875869-8792-4c92-946b-9cbc3d9a6ddb
-- title:
--   Random scalar cube tuples fail to be good scalar kernel tuples with probability at most the adjusted accuracy
-- statement:
--   All named objects below are defined by OpenAI. Let $I$ be a nonempty finite type and $J$ a finite type, both with decidable equality, with $|I|\,(|I|+2) \le |J|$, and let $s : I \hookrightarrow J$ be an embedding. Let $M, D, L$ be natural numbers and $\eta$ a real number with $0 < M$, $0 < D$, $0 < \eta$ and $0 < L$. Write $K$ = `scalarKernelCutoff I J M D η`, an explicit natural number defined by OpenAI, and assume $K \le L$.
--
--   Let $x = (x_j)_{j \in J}$ be random, with the $x_j$ independent and each distributed according to `integerScalarCubeWeights I L hL`: the uniform distribution on the set of integer scalar cubes in `IntegerScalarCubeBox I L`, i.e. on the vectors $y$ indexed by `Option I` with entries in $[-L, L)$ such that $0 \le y_{\mathrm{none}} + \sum_{i \in t} y_{\mathrm{some}\ i} < L$ for every $t \subseteq I$. Then the probability that $x$ is not a `GoodScalarKernelTuple s (1/K) K` is at most `scalarKernelAdjustedAccuracy I J M D η` $= \eta / (\texttt{scalarCubeResidueDensityCap}\ I\ (MD))^{|J|}$.
--
--   Here `GoodScalarKernelTuple s κ B x` means: $\kappa < |\texttt{normalizedScalarCubeMinor}\ s\ x|$, where the normalized minor is $\det(A_s)/L^{|I|}$ with $A$ the integer $I \times J$ matrix with entries $A_{i,j} = (x_j)_{\mathrm{some}\ i}$ (`scalarCubeDifferenceMatrix x`) and $A_s$ its square submatrix on the columns $s(I)$; and the range of $A$ (as a subgroup of $\mathbb{Z}^I$) has bounded period $B$ (`HasBoundedScalarPeriod`: there is a natural number $a$ with $0 < a \le B$ such that $a\mathbb{Z}^I$ is contained in the range).
--
--   Lean: `OAI.Erdos3.scalarKernel_explicit_probability_le_of_card_le_s2`, which states OpenAI's `OAI.Erdos3.scalarKernel_explicit_probability_le_of_card_le` (in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedAveragedCoarseKernelComparison.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B065`, `OAIE3v2B093` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedAveragedCoarseKernelComparison.lean (declaration OAI.Erdos3.scalarKernel_explicit_probability_le_of_card_le)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B065
import Definitions.Def_OAIE3v2B093

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scalarKernel_explicit_probability_le_of_card_le_s2 (I J : Type*)
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J) (s : I ↪ J)
    {M D L : ℕ} {η : ℝ} (hM : 0 < M) (hD : 0 < D) (hη : 0 < η) (hL : 0 < L)
    (hlarge : scalarKernelCutoff I J M D η ≤ L) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
      (fun x => ¬ GoodScalarKernelTuple s (1 / (scalarKernelCutoff I J M D η : ℝ))
        (scalarKernelCutoff I J M D η) x) ≤ scalarKernelAdjustedAccuracy I J M D η := by
  sorry

end Erdos3

end

end OAI
end
