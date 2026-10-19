-- Prove2me | Theorems.Thm_OAI_Erdos3_productANOVASectionTensor_bound_of_normalized_s2
-- name    : OAI.Erdos3.productANOVASectionTensor_bound_of_normalized_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:19:49.797992+00:00
-- url     : https://prove2.me/theorems/9cc985b7-c6fb-4cc3-881a-1981fc75f2cb
-- title:
--   An L2 bound for the ANOVA section tensor from bounds on the degree-d ANOVA energy of normalized sections
-- statement:
--   Let $I$ be a finite linearly ordered type, $X_i$ ($i \in I$) finite types, and $\mu_i$ a probability law on $X_i$ for each $i$; let $\mu = \prod_i \mu_i$ be the product law on $\prod_i X_i$. For a set $S \subseteq I$ and $f : \prod_i X_i \to \mathbb{R}$, `productANOVA μ S f` (defined by OpenAI) is the ANOVA (Efron–Stein) component $\sum_{U \subseteq S} (-1)^{|U|}\, \mathbb{E}_\mu[f \mid \text{coordinates in } S \setminus U]$, and for a family $\mathcal{D}$ of sets, `productANOVAEnergy μ 𝒟 f` $= \sum_{S \in \mathcal{D}} \mathbb{E}_\mu[(\texttt{productANOVA}\ \mu\ S\ f)^2]$. For $T, A \subseteq I$ and points $z, x$, write $\mathrm{mix}_S(x, y)$ for the point equal to $x$ on $S$ and $y$ off $S$; `productSectionAverage μ T A z f x` $= \mathbb{E}_{y \sim \mu} f\bigl(\mathrm{mix}_T(\mathrm{mix}_A(z, y), x)\bigr)$ and `productNormalizedSection μ T A z K f` $= K^{-|A|} \cdot$ `productSectionAverage μ T A z f` (both defined by OpenAI).
--
--   Let $T \subseteq I$ be a finite set, $d \in \mathbb{N}$, $z, \mathrm{base} \in \prod_i X_i$, $K > 0$, $B \in \mathbb{R}$, and $f : \prod_i X_i \to \mathbb{R}$. Assume that for every $A \subseteq T$,
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \binom{I}{d}\ \bigl(\texttt{productNormalizedSection}\ \mu\ T\ A\ z\ K\ f\bigr)} \le B,$$
--   where $\binom{I}{d}$ is the family of $d$-element subsets of $I$. Then
--   $$\sqrt{\sum_{v : \mathrm{Fin}\,d \to \Sigma_i X_i} \Bigl(\prod_{k} \mu_{v_k.1}(v_k.2)\Bigr)\, \bigl(\texttt{productANOVASectionTensor}\ \mu\ T\ d\ z\ \mathrm{base}\ f\ v\bigr)^2} \;\le\; (1 + K)^{|T|}\, B.$$
--   Here the sum is `finiteProductIntegral` with the weights `coordinateUnionWeight μ` (the weight of $(i, x_i)$ is $\mu_i(x_i)$), and `productANOVASectionTensor μ T d z base f v` (defined by OpenAI) is $0$ unless the indices $v_1.1 < \dots < v_d.1$ are strictly increasing, in which case, with $U = \{v_1.1, \dots, v_d.1\}$ and $x$ the point with coordinates $v_k.2$ at $v_k.1$ and $\mathrm{base}$ elsewhere, it equals $\texttt{productANOVA}\ \mu\ (T \cup U)\ f\ (\mathrm{mix}_T(z, x))$ if $T$ and $U$ are disjoint and $0$ otherwise.
--
--   Lean: `OAI.Erdos3.productANOVASectionTensor_bound_of_normalized_s2`, which states OpenAI's `OAI.Erdos3.productANOVASectionTensor_bound_of_normalized` (in `lean/OAI/Combinatorics/Progressions/Linear/ProductANOVASectionNormalizedBound.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B127`, `OAIE3v2B139` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/ProductANOVASectionNormalizedBound.lean (declaration OAI.Erdos3.productANOVASectionTensor_bound_of_normalized)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B127
import Definitions.Def_OAIE3v2B139

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVASectionTensor_bound_of_normalized_s2 (T : Finset I) (d : ℕ)
    (z base : ∀ i, X i) {K B : ℝ} (hK : 0 < K) (f : (∀ i, X i) → ℝ)
    (hLower : ∀ A ⊆ T,
      Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard d)
        (productNormalizedSection μ T A z K f)) ≤ B) :
    Real.sqrt (finiteProductIntegral (fun _ : Fin d => coordinateUnionWeight μ)
      (fun v => productANOVASectionTensor μ T d z base f v ^ 2)) ≤ (1 + K) ^ T.card * B := by
  sorry

end Erdos3

end

end OAI
end
