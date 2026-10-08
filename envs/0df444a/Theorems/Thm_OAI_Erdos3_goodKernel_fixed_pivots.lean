-- Prove2me | Theorems.Thm_OAI_Erdos3_goodKernel_fixed_pivots
-- name    : OAI.Erdos3.goodKernel_fixed_pivots
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:20:56.04098+00:00
-- url     : https://prove2.me/theorems/2ef6f656-b504-400e-8c95-ea1cf99fde54
-- title:
--   A good kernel tuple has nonsingular jet pivots with bounded normalized inverses
-- statement:
--   Let $Q$ be a type, $\alpha$ and $J$ finite types with decidable equality, and $O : Q\to$ types, each $O_q$ finite with decidable equality. Let $L,B$ be natural numbers and $\kappa$ a real number with $0<L$ and $0<\kappa$, and let $\mathrm{selection} : \alpha\hookrightarrow J$ be an embedding. Let $x : J\to$ `IntegerScalarCubeBox α L` (functions from $\mathrm{Option}\ \alpha$ to the integers in $[-L,L)$) satisfy `GoodScalarKernelTuple selection κ B x`: the normalized minor `normalizedScalarCubeMinor selection x` (the determinant of the $\alpha\times\alpha$ submatrix, with columns selected by $\mathrm{selection}$, of the integer matrix `scalarCubeDifferenceMatrix x` whose $(i,j)$ entry is $x_j(\mathrm{some}\ i)$, divided by $L^{|\alpha|}$) has absolute value greater than $\kappa$, and the column span over $\mathbb{Z}$ of `scalarCubeDifferenceMatrix x` contains $a\,\mathbb{Z}^\alpha$ for some natural number $0<a\le B$ (`HasBoundedScalarPeriod`). Let $\mathrm{degree} : Q\to\mathbb{N}$ and, for each $q$, let $\mathrm{rows}_q : O_q\to\mathrm{Finset}\ \alpha$ be injective with $|\mathrm{rows}_q(i)|\le\mathrm{degree}_q$ for all $i$. Then there exist, for each $q$, an embedding $s_q$ of $O_q$ into `BoundedIntegerExponent J (degree q)` (the finitely supported exponent vectors $e : J\to\mathbb{N}$ with $\sum_j e_j\le\mathrm{degree}_q$), such that for each $q$ the square submatrix of `scalarKernelIntegerJet x (degree q) (rows q)` (OpenAI's integer jet matrix, rows indexed by $O_q$ and columns by `BoundedIntegerExponent J (degree q)`) with columns selected by $s_q$ has nonzero determinant, and for every $q$ the operator norm of the inverse of the linear isomorphism `scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)` of $\mathbb{R}^{O_q}$ (OpenAI's normalized pivot isomorphism built from that submatrix with OpenAI's column scales `kernelJetCoefficientScale`) is at most `kernelJetInverseAllowance |α| |J| |O q| (degree q) κ`, a real number defined by OpenAI from these parameters.
--
--   Lean: `OAI.Erdos3.goodKernel_fixed_pivots` in `lean/OAI/Combinatorics/Progressions/Linear/KernelCoefficientLogBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/KernelCoefficientLogBudget.lean#L219

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem goodKernel_fixed_pivots {Q α J : Type*}
    [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    {O : Q → Type*} [∀ q, Fintype (O q)] [∀ q, DecidableEq (O q)]
    {L B : ℕ} {κ : ℝ} (hL : 0 < L) (selection : α ↪ J) (hκ : 0 < κ)
    (x : J → IntegerScalarCubeBox α L) (hx : GoodScalarKernelTuple selection κ B x)
    (degree : Q → ℕ) (rows : ∀ q, O q → Finset α)
    (hinj : ∀ q, Function.Injective (rows q)) (hrows : ∀ q i, (rows q i).card ≤ degree q) :
    ∃ s : ∀ q, O q ↪ BoundedIntegerExponent J (degree q),
    ∃ hs : ∀ q, ((scalarKernelIntegerJet x (degree q) (rows q)).submatrix id (s q)).det ≠ 0,
      ∀ q, ‖(scalarKernelFixedPivot hL x (degree q) (rows q) (s q) (hs q)).symm.toContinuousLinearMap‖ ≤
        kernelJetInverseAllowance (Fintype.card α) (Fintype.card J) (Fintype.card (O q)) (degree q) κ := by
  sorry

end Erdos3
end
end OAI
