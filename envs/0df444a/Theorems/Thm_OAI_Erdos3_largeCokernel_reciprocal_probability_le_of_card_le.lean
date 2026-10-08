-- Prove2me | Theorems.Thm_OAI_Erdos3_largeCokernel_reciprocal_probability_le_of_card_le
-- name    : OAI.Erdos3.largeCokernel_reciprocal_probability_le_of_card_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:24:57.973367+00:00
-- url     : https://prove2.me/theorems/0ed822ab-32eb-45ba-99fd-6c99e3ff2022
-- title:
--   Large-cokernel probability bound from reciprocal-root single-column character bounds
-- statement:
--   Let $I$ be a nonempty finite type and $J$ a finite type (both with decidable equality), with $|I|(|I|+2)\le |J|$. For each $j\in J$ let $\Omega_j$ be a finite type carrying `FiniteProbabilityWeights` $p_j$ (a structure bundling nonnegative weights on $\Omega_j$ summing to $1$), and let $\mathrm{column}_j\colon\Omega_j\to(I\to\mathbb Z)$. Let $B,R\in\mathbb N$ with $0<B$, and $C\ge 0$ real. Assume `hsingle`: for every natural number $a$ with $B<a\le R$, every additive character $\chi\colon \mathbb Z^I\to\mathbb C$ of order $a$, and every $j\in J$, the $p_j$-probability that $\chi(\mathrm{column}_j(x))=1$ is at most $C/a^{1/|I|}$. Then, under the product weights `FiniteProbabilityWeights.pi p` (weight $\prod_j p_j(x_j)$ on $\prod_j\Omega_j$), the probability of `largeCokernelEvent column B R` is at most $C^{|J|}/B$. Here `largeCokernelEvent column B R x` says: there is a square integer matrix $A\in\mathbb Z^{I\times I}$ with $\det A\ne 0$, whose column span is contained in the column span of the sampled matrix $M_x=(\mathrm{column}_j(x_j)_i)_{i\in I,j\in J}$ (`sampledColumnMatrix column x`), with $|\det A|\le R$, and such that $B<$ `integerCokernelExponent` of the column span of $M_x$, the exponent of the additive group $\mathbb Z^I/\operatorname{span}_{\mathbb Z}(M_x)$.
--
--   Lean: `OAI.Erdos3.largeCokernel_reciprocal_probability_le_of_card_le` in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedAveragedCoarseKernelComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedAveragedCoarseKernelComparison.lean#L57

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem largeCokernel_reciprocal_probability_le_of_card_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) (column : ∀ j, Ω j → I → ℤ)
    (B R : ℕ) (hB : 0 < B) (C : ℝ) (hC : 0 ≤ C)
    (hJ : Fintype.card I * (Fintype.card I + 2) ≤ Fintype.card J)
    (hsingle : ∀ (a : ℕ), B < a → a ≤ R → ∀ χ : AddChar (I → ℤ) ℂ,
      orderOf χ = a → ∀ j, (p j).eventProbability (fun x => χ (column j x) = 1) ≤
        C / (a : ℝ) ^ (1 / (Fintype.card I : ℝ))) :
    (FiniteProbabilityWeights.pi p).eventProbability (largeCokernelEvent column B R) ≤
      C ^ Fintype.card J / (B : ℝ) := by
  sorry

end Erdos3
end
end OAI
