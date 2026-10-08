-- Prove2me | Theorems.Thm_OAI_Erdos3_productANOVATensor_uniform_of_normalized
-- name    : OAI.Erdos3.productANOVATensor_uniform_of_normalized
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:26:57.069981+00:00
-- url     : https://prove2.me/theorems/2512366f-5829-4e83-841c-11bbc2ee7122
-- title:
--   Section norms of the ANOVA tensor from bounds on normalized sections
-- statement:
--   Let $I$ be a finite linearly ordered type, $X_i$ ($i\in I$) finite types, and $\mu=(\mu_i)$ a family of `FiniteProbabilityWeights` on the $X_i$ (section variables), with product weights $\pi=$ `FiniteProbabilityWeights.pi μ` on $\prod_iX_i$. For $S\subseteq I$ write $\mathbb E_Sf(x)$ (`productConditionalMean μ S f x`) for the $\pi$-mean over $y$ of $f$ at the point equal to $x$ on $S$ and to $y$ off $S$; `productANOVA μ S f` is $f_S=\sum_{U\subseteq S}(-1)^{|U|}\,\mathbb E_{S\setminus U}f$; and `productANOVAEnergy μ D f` is $\sum_{S\in D}\mathbb E_\pi[f_S^2]$. Let $n\in\mathbb N$, `base` $\in\prod_iX_i$, reals $K,R$ with $1\le K$ and $1+K\le R$, and $f\colon\prod_iX_i\to\mathbb R$. Assume `hLower`: for every $T\subseteq I$ with $0<|T|\le n$, every $a$ with $\pi(a)\ne0$ and every $A\subseteq T$,
--   $$\sqrt{\texttt{productANOVAEnergy}\ \mu\ \{S:|S|=n-|T|\}\ (\texttt{productNormalizedSection}\ \mu\ T\ A\ a\ K\ f)}\le R^{2(n-|T|)},$$
--   where `productNormalizedSection μ T A a K f x` is $K^{-|A|}$ times the $\pi$-mean over $y$ of $f$ at the point equal to $a$ on $T\cap A$, to $y$ on $T\setminus A$ and to $x$ off $T$. Then for every $s\colon\mathrm{Fin}\,n\to\mathrm{Bool}$ and $z\colon\mathrm{Fin}\,n\to\Sigma_iX_i$,
--   `finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) n s (productANOVATensor μ n base f) z` $\le\max\big(\sqrt{\texttt{productANOVAEnergy}\ \mu\ \{S:|S|=n\}\ f},\ R^{2n-1}\big)$.
--   Here `coordinateUnionWeight μ` is the weight $(i,a)\mapsto\mu_i(a)$ on $\Sigma_iX_i$; `productANOVATensor μ n base f` is the function on $(\Sigma_iX_i)^n$ that at $z=((i_1,a_1),\dots,(i_n,a_n))$ with $i_1<\dots<i_n$ and $\prod_j\mu_{i_j}(a_j)\ne0$ equals $f_{\{i_1,\dots,i_n\}}$ evaluated at the point with coordinate $a_j$ at $i_j$ and `base` elsewhere, and is $0$ otherwise; and `finiteSectionL2Norm w n s g z` is the square root of the partial integral of $g^2$ in which the positions $j$ with $s_j$ true are fixed to $z_j$ and the other positions are summed against the weight $w$. The exponents $n-|T|$ and $2n-1$ are natural-number subtractions.
--
--   Lean: `OAI.Erdos3.productANOVATensor_uniform_of_normalized` in `lean/OAI/Combinatorics/Progressions/Estimates/ProductTensorNormalizedUniform.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ProductTensorNormalizedUniform.lean#L64

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVATensor_uniform_of_normalized (n : ℕ) (base : ∀ i, X i)
    {K R : ℝ} (hK : 1 ≤ K) (hR : 1 + K ≤ R) (f : (∀ i, X i) → ℝ)
    (hLower : ∀ T : Finset I, 0 < T.card → T.card ≤ n → ∀ a : ∀ i, X i,
      (FiniteProbabilityWeights.pi μ).weight a ≠ 0 → ∀ A ⊆ T,
        Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard (n - T.card))
          (productNormalizedSection μ T A a K f)) ≤ R ^ (2 * (n - T.card)))
    (s : Fin n → Bool) (z : Fin n → Sigma X) :
    finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) n s (productANOVATensor μ n base f) z ≤
      max (Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard n) f)) (R ^ (2 * n - 1)) := by
  sorry

end Erdos3
end
end OAI
