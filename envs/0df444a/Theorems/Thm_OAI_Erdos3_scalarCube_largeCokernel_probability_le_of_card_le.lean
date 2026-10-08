-- Prove2me | Theorems.Thm_OAI_Erdos3_scalarCube_largeCokernel_probability_le_of_card_le
-- name    : OAI.Erdos3.scalarCube_largeCokernel_probability_le_of_card_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:26:48.749986+00:00
-- url     : https://prove2.me/theorems/f3d7e14f-eede-4d47-931b-c7eb8f547d93
-- title:
--   Independent integer scalar cubes rarely span a lattice of large cokernel exponent
-- statement:
--   Let $I$ be a nonempty finite type and $J$ a finite type (both with decidable equality), and let $L,B\in\mathbb N$ with $0<L$, $|I|+1\le L$, $0<B$, and $|I|(|I|+2)\le|J|$. Sample $x=(x_j)_{j\in J}$ independently from the product weights `FiniteProbabilityWeights.pi (fun _ => integerScalarCubeWeights I L hL)`. Then the probability of `scalarCubeLargeCokernelEvent B` is at most
--   $$\big(\texttt{integerScalarCubeDensityCap}\ I\cdot(1+|I|!)\big)^{|J|}/B .$$
--   Here `IntegerScalarCubeBox I L` is the finite type of functions $\mathrm{Option}\,I\to\{-L,\dots,L-1\}$; `integerScalarCubeWeights I L hL` is the uniform probability on this box conditioned on the set of $y$ satisfying `IntegerScalarCube L`, i.e. $0\le y(\mathrm{none})+\sum_{i\in t}y(\mathrm{some}\ i)<L$ for every finite $t\subseteq I$; `integerScalarCubeDensityCap I` is the real number $(4(|I|+1))^{|I|+1}$; and `scalarCubeLargeCokernelEvent B x` says that the integer matrix $M_x=(x_j(\mathrm{some}\ i))_{i\in I,j\in J}$ (`scalarCubeDifferenceMatrix x`) has an $I\times I$ column submatrix $(M_x)_{\cdot,s}$, $s\colon I\to J$, with nonzero determinant, and that $B<$ `integerCokernelExponent` of the column span of $M_x$, the exponent of the additive group $\mathbb Z^I/\operatorname{span}_{\mathbb Z}(M_x)$.
--
--   Lean: `OAI.Erdos3.scalarCube_largeCokernel_probability_le_of_card_le` in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedAveragedCoarseKernelComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedAveragedCoarseKernelComparison.lean#L102

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scalarCube_largeCokernel_probability_le_of_card_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    (L B : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L) (hB : 0 < B)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).eventProbability
        (scalarCubeLargeCokernelEvent B) ≤
      (integerScalarCubeDensityCap I * (1 + ((Fintype.card I).factorial : ℝ))) ^
        Fintype.card J / (B : ℝ) := by
  sorry

end Erdos3
end
end OAI
