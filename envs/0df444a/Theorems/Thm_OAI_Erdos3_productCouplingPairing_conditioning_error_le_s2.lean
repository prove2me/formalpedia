-- Prove2me | Theorems.Thm_OAI_Erdos3_productCouplingPairing_conditioning_error_le_s2
-- name    : OAI.Erdos3.productCouplingPairing_conditioning_error_le_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:25:35.110197+00:00
-- url     : https://prove2.me/theorems/dde4b2cd-27a0-4b23-9b77-a64a0f2894b3
-- title:
--   Conditioning a low-degree coupled pairing on a fiber costs at most 2^|I| times the shell error
-- statement:
--   Let $\iota$ be a finite type with decidable equality. For each $i \in \iota$ let $X_i, Y_i$ be finite types carrying probability weights $\mu_i$ on $X_i$ and $\nu_i$ on $Y_i$ (OpenAI `FiniteProbabilityWeights`: nonnegative weights summing to $1$), and let $c_i$ be a coupling of $\mu_i$ and $\nu_i$ (an OpenAI `FiniteProbabilityCoupling`: probability weights on $X_i \times Y_i$ whose two marginals are $\mu_i$ and $\nu_i$). Write $\mu = \prod_i \mu_i$ and $\nu = \prod_i \nu_i$ for the product weights. We use the following OpenAI definitions.
--   - For $f : \prod_i X_i \to \mathbb{R}$ and $g : \prod_i Y_i \to \mathbb{R}$, `productCouplingPairing c f g` is the mean of $f(z_1)\,g(z_2)$ when $z = (z_1, z_2)$ is distributed according to the product of the couplings $c_i$.
--   - For a set $S \subseteq \iota$, the ANOVA component of $f$ is $f_S(x) = \sum_{U \subseteq S} (-1)^{|U|}\, \mathbb{E}_{y \sim \mu}\, f(x|_{S \setminus U}, y|_{\text{rest}})$, where $(x|_{T}, y|_{\text{rest}})$ is the point equal to $x$ on $T$ and to $y$ off $T$; for a finite family $\mathcal{D}$ of subsets of $\iota$, `productANOVATruncation μ 𝒟 f` $= \sum_{S \in \mathcal{D}} f_S$. The same definitions with $\nu$ apply on the $Y$ side.
--   - `lowDegreeCoordinateSets ι b` is the family of all subsets of $\iota$ with at most $b$ elements.
--   - For $I \subseteq \iota$, `conditioningCoreSupports I b` is the family of subsets $B$ of the complement $\iota \setminus I$ with $|B| \le b - |I|$, and for $A \subseteq I$, `conditioningShellSupports I A b` is the family of subsets $B \subseteq \iota \setminus I$ with $b - |I| < |B|$ and $|A| + |B| \le b$ (natural-number subtraction).
--   - `productSectionAverage μ I I x w` is the function $x' \mapsto \mathbb{E}_{y \sim \mu}\, w(m)$, where $m$ agrees with $x$ on $I$ and with $x'$ off $I$ (it is obtained by mixing first $x$ with $y$ on $I$ and then the result with $x'$ on $I$); similarly on the $Y$ side with $\nu$.
--   - `productFiberIndicator I x z` is $1$ if $z_i = x_i$ for all $i \in I$ and $0$ otherwise.
--   - `productCouplingAtomMass c I x y` is the total mass, under the product of the couplings $c_i$, of the set of pairs $(z_1, z_2)$ with $(z_1)_i = x_i$ and $(z_2)_i = y_i$ for all $i \in I$.
--
--   Now let $I \subseteq \iota$ and let $b$ be a natural number with $|I| \le b$. Let $x \in \prod_i X_i$, $y \in \prod_i Y_i$, $w : \prod_i X_i \to \mathbb{R}$, $f : \prod_i Y_i \to \mathbb{R}$ and $E \in \mathbb{R}$. Write $w_I = $ `productSectionAverage μ I I x w` and $f_I = $ `productSectionAverage ν I I y f`. Assume that for every $A \subseteq I$,
--   $$\Bigl|\texttt{productCouplingPairing}\ c\ \bigl(\texttt{productANOVATruncation}\ \mu\ (\texttt{conditioningShellSupports}\ I\ A\ b)\ w_I\bigr)\ \bigl(\texttt{productANOVATruncation}\ \nu\ (\texttt{conditioningShellSupports}\ I\ A\ b)\ f_I\bigr)\Bigr| \le E.$$
--   Then
--   $$\Bigl|\texttt{productCouplingPairing}\ c\ \bigl(\texttt{productANOVATruncation}\ \mu\ \mathcal{L}_b\ \tilde w\bigr)\ \bigl(\texttt{productANOVATruncation}\ \nu\ \mathcal{L}_b\ \tilde f\bigr) - M \cdot \texttt{productCouplingPairing}\ c\ \bigl(\texttt{productANOVATruncation}\ \mu\ \mathcal{C}\ w_I\bigr)\ \bigl(\texttt{productANOVATruncation}\ \nu\ \mathcal{C}\ f_I\bigr)\Bigr| \le 2^{|I|} E,$$
--   where $\mathcal{L}_b = $ `lowDegreeCoordinateSets ι b`, $\mathcal{C} = $ `conditioningCoreSupports I b`, $M = $ `productCouplingAtomMass c I x y`, $\tilde w(z) = $ `productFiberIndicator I x z` $\cdot\, w(z)$ and $\tilde f(z) = $ `productFiberIndicator I y z` $\cdot\, f(z)$.
--
--   Lean: `OAI.Erdos3.productCouplingPairing_conditioning_error_le_s2`, which states OpenAI's `OAI.Erdos3.productCouplingPairing_conditioning_error_le` (in `lean/OAI/Combinatorics/Progressions/Estimates/ConditioningShellError.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B126`, `OAIE3v2B138` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ConditioningShellError.lean (declaration OAI.Erdos3.productCouplingPairing_conditioning_error_le)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B138

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

theorem productCouplingPairing_conditioning_error_le_s2 (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    {E : ℝ}
    (hshell : ∀ A ∈ I.powerset, |productCouplingPairing c
      (productANOVATruncation μ (conditioningShellSupports I A b) (productSectionAverage μ I I x w))
      (productANOVATruncation ν (conditioningShellSupports I A b) (productSectionAverage ν I I y f))| ≤ E) :
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * E := by
  sorry

end Erdos3

end

end OAI
end
