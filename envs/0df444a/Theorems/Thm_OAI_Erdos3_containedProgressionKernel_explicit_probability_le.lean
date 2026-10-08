-- Prove2me | Theorems.Thm_OAI_Erdos3_containedProgressionKernel_explicit_probability_le
-- name    : OAI.Erdos3.containedProgressionKernel_explicit_probability_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:03:59.285994+00:00
-- url     : https://prove2.me/theorems/fce6c4ce-8e53-4466-8436-6884e9cc9728
-- title:
--   Under the contained-progression cube law, a non-good kernel tuple has probability at most η
-- statement:
--   Let $\alpha$ be a nonempty finite type with decidable equality and $K$ a finite type with decidable equality, with $|\alpha|\,(|\alpha|+2)\le|K|$, and let $\mathrm{selection} : \alpha\hookrightarrow K$ be an embedding. Let $L,D$ be natural numbers and $\eta$ a real number with $0<L$, $0<D$, $0<\eta$, and $\mathrm{cut}\le L$, where $\mathrm{cut}$ is the natural number `scalarKernelCutoff α K 1 D η` (an explicit cutoff defined by OpenAI). Let $H,\mathrm{step} : K\to\mathbb{N}$ and $c : K\to\mathbb{Z}$ with $H_k>0$, $\mathrm{step}_k>0$ and $L\le D\cdot H_k$ for every $k$, and with `integerProgressionSupport (c k) (step k) (H k)` (the set $\{c_k+\mathrm{step}_k\,t : 0\le t<H_k\}$) contained in $\{0,\dots,L-1\}$ for every $k$. Let $\lambda$ be `containedProgressionCubeLaw (fun _ => L) H step c …`, the probability weights on families $(x_k)_{k\in K}$ with $x_k\in$ `IntegerScalarCubeBox α L` obtained as the push-forward, under the coordinatewise `containedProgressionCubeMap` (sending an integer scalar cube $z$ of size $H_k$ to $i\mapsto[i=\mathrm{none}]\,c_k+\mathrm{step}_k\,z_i$), of the product of OpenAI's uniform laws `integerScalarCubeWeights α (H k)` on integer scalar cubes. Then the $\lambda$-probability (`eventProbability`) of the event that $x$ fails `GoodScalarKernelTuple selection (1/cut) cut x` is at most $\eta$; here `GoodScalarKernelTuple s κ B x` is the predicate that $|$`normalizedScalarCubeMinor s x`$|>\kappa$ and the range of the integer matrix `scalarCubeDifferenceMatrix x` satisfies `HasBoundedScalarPeriod … B` (it contains $a\,\mathbb{Z}^{\alpha}$ for some natural number $0<a\le B$).
--
--   Lean: `OAI.Erdos3.containedProgressionKernel_explicit_probability_le` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedRowsProjectedSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B012` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedRowsProjectedSource.lean#L126

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B012

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {L H step : ℕ} (c : ℤ) (hL : 0 < L) (hH : 0 < H) (hstep : 0 < step)
variable (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))

theorem containedProgressionKernel_explicit_probability_le
    {K : Type*} [Fintype K] [DecidableEq K] [Nonempty α]
    (hK : Fintype.card α * (Fintype.card α + 2) ≤ Fintype.card K) (selection : α ↪ K)
    {L D : ℕ} {η : ℝ} (hL : 0 < L) (hD : 0 < D) (hη : 0 < η)
    (hlarge : scalarKernelCutoff α K 1 D η ≤ L)
    (H step : K → ℕ) (c : K → ℤ) (hH : ∀ k, 0 < H k) (hstep : ∀ k, 0 < step k)
    (hLH : ∀ k, L ≤ D * H k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L : ℤ)) :
    (containedProgressionCubeLaw (α := α) (fun _ => L) H step c (fun _ => hL) hH hsubset).eventProbability
      (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
        (scalarKernelCutoff α K 1 D η) x) ≤ η := by
  sorry

end Erdos3
end
end OAI
