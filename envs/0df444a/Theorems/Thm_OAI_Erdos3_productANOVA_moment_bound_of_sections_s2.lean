-- Prove2me | Theorems.Thm_OAI_Erdos3_productANOVA_moment_bound_of_sections_s2
-- name    : OAI.Erdos3.productANOVA_moment_bound_of_sections_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:23:48.807386+00:00
-- url     : https://prove2.me/theorems/58f7848c-d22c-4a5c-a120-623c0d092ab8
-- title:
--   A moment bound for the degree-k ANOVA part of a function on a finite product space from section L2 bounds
-- statement:
--   All named objects below are defined by OpenAI. Let $I$ be a finite linearly ordered type, $X_i$ ($i \in I$) finite types, and $\mu_i$ a finite probability distribution on $X_i$ for each $i$; let $\mu = \prod_i \mu_i$ be the product distribution on $\prod_i X_i$. Let $k, q$ be natural numbers, `base` $\in \prod_i X_i$, $x_0$ an element of the disjoint union $\Sigma_i X_i$ (it only serves to make this type nonempty), $f : \prod_i X_i \to \mathbb{R}$, and $B \ge 0$ a real number. Assume that for every $t \in \{\mathrm{true}, \mathrm{false}\}^k$ and every $z \in (\Sigma_i X_i)^k$,
--   $$\texttt{finiteSectionL2Norm}\ (\_ \mapsto \texttt{coordinateUnionWeight}\ \mu)\ k\ t\ (\texttt{productANOVATensor}\ \mu\ k\ \mathrm{base}\ f)\ z \le B.$$
--   Here `coordinateUnionWeight μ (i, a)` $= \mu_i(a)$; `finiteSectionL2Norm w k t F z` is the square root of the iterated sum of $F^2$ in which, for each position $j < k$ with $t_j = $ false, the $j$-th argument is summed against the weight $w$, while the positions with $t_j = $ true are fixed to $z_j$; and `productANOVATensor μ k base f z` is $0$ unless the indices of $z_0, \dots, z_{k-1}$ are strictly increasing and all their weights are nonzero, in which case it is the ANOVA component of $f$ on the set of those indices, evaluated at the point that agrees with the $z_j$ at those indices and with `base` elsewhere.
--
--   Then
--   $$\Bigl|\mathbb{E}_{x \sim \mu}\Bigl(\sum_{S \subseteq I,\ |S| = k} \texttt{productANOVA}\ \mu\ S\ f\ x\Bigr)^q\Bigr| \le (qk)^{qk}\,B^q,$$
--   where `productANOVA μ S f x` $= \sum_{U \subseteq S} (-1)^{|U|}\,\mathbb{E}_{y \sim \mu} f(\text{the point equal to } x \text{ on } S \setminus U \text{ and to } y \text{ elsewhere})$ is the ANOVA (Efron–Stein) component of $f$ on $S$.
--
--   Lean: `OAI.Erdos3.productANOVA_moment_bound_of_sections_s2`, which states OpenAI's `OAI.Erdos3.productANOVA_moment_bound_of_sections` (in `lean/OAI/Combinatorics/Progressions/Linear/ProductANOVAWeightedLp.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B139` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/ProductANOVAWeightedLp.lean (declaration OAI.Erdos3.productANOVA_moment_bound_of_sections)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B139

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_moment_bound_of_sections_s2 (k q : ℕ) (base : ∀ i, X i) (x₀ : Sigma X)
    (f : (∀ i, X i) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base f) z ≤ B) :
    |(FiniteProbabilityWeights.pi μ).mean
      (fun x => (∑ S ∈ Finset.univ.powersetCard k, productANOVA μ S f x) ^ q)| ≤
        ((q * k) ^ (q * k) : ℕ) * B ^ q := by
  sorry

end Erdos3

end

end OAI
end
