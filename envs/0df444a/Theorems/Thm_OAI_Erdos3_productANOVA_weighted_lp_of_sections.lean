-- Prove2me | Theorems.Thm_OAI_Erdos3_productANOVA_weighted_lp_of_sections
-- name    : OAI.Erdos3.productANOVA_weighted_lp_of_sections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T11:39:04.808716+00:00
-- url     : https://prove2.me/theorems/2f9bea45-eea3-4af3-86fe-93e1ccf714d0
-- title:
--   Weighted L^q bound for a degree-k ANOVA truncation from section norm bounds
-- statement:
--   Let $I$ be a finite linearly ordered type, $X_i$ ($i\in I$) finite types, and $\mu=(\mu_i)$ a family of `FiniteProbabilityWeights` on the $X_i$ (section variables), with product weights $\pi=$ `FiniteProbabilityWeights.pi μ`. For $S\subseteq I$ let $\mathbb E_Sg(x)$ (`productConditionalMean μ S g x`) be the $\pi$-mean over $y$ of $g$ at the point equal to $x$ on $S$ and $y$ off $S$, and let `productANOVA μ S g` be $g_S=\sum_{U\subseteq S}(-1)^{|U|}\mathbb E_{S\setminus U}g$. Let $\rho,F\colon\prod_iX_i\to\mathbb R$ with $\rho\ge0$, reals $M\ge0$, $\eta\ge0$ with $0\le F\le M$, natural numbers $k,q$ with $q>0$ even, `base` $\in\prod_iX_i$, $x_0\in\Sigma_iX_i$, and $C\ge0$. Assume `ProductMarginalsClose μ ρ η (q*k)`, i.e. $|\mathbb E_B\rho(x)-1|\le\eta$ for every $B\subseteq I$ with $|B|\le qk$ and every $x$ with $\pi(x)\ne0$; assume $\eta\,\big(2^k|I|^kM(1+\eta)\big)^q\le1$; and assume `hsection`: for all $t\colon\mathrm{Fin}\,k\to\mathrm{Bool}$ and $z\colon\mathrm{Fin}\,k\to\Sigma_iX_i$, `finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t (productANOVATensor μ k base (ρ·F)) z` $\le C$. Then
--   $$\Big(\sum_x\pi(x)\rho(x)\,\Big|\sum_{|S|=k}(\rho F)_S(x)\Big|^q\Big)^{1/q}\le (qk)^k\,C+1,$$
--   the left side being `finiteWeightedLp (π·ρ) q (productANOVATruncation μ {S : |S| = k} (ρ·F))`. Here `coordinateUnionWeight μ` is $(i,a)\mapsto\mu_i(a)$ on $\Sigma_iX_i$; `productANOVATensor μ k base g` is the function on $(\Sigma_iX_i)^k$ that at $((i_1,a_1),\dots,(i_k,a_k))$ with $i_1<\dots<i_k$ and $\prod_j\mu_{i_j}(a_j)\ne0$ equals $g_{\{i_1,\dots,i_k\}}$ at the point with coordinate $a_j$ at $i_j$ and `base` elsewhere, and is $0$ otherwise; `finiteSectionL2Norm w k t h z` is the square root of the partial integral of $h^2$ with positions $j$ where $t_j$ is true fixed to $z_j$ and the others summed against $w$. The point $x_0$ does not appear in the hypotheses or the conclusion.
--
--   Lean: `OAI.Erdos3.productANOVA_weighted_lp_of_sections` in `lean/OAI/Combinatorics/Progressions/Linear/ProductANOVAWeightedLp.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B014` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/ProductANOVAWeightedLp.lean#L117

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [LinearOrder I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productANOVA_weighted_lp_of_sections (rho F : (∀ i, X i) → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ M) (k q : ℕ) (hq : 0 < q) (heven : Even q)
    (base : ∀ i, X i) (x₀ : Sigma X) (C : ℝ) (hC : 0 ≤ C)
    (hclose : ProductMarginalsClose μ rho eta (q * k))
    (herr : eta * ((2 : ℝ) ^ k * (Fintype.card I : ℝ) ^ k * M * (1 + eta)) ^ q ≤ 1)
    (hsection : ∀ t z, finiteSectionL2Norm (fun _ => coordinateUnionWeight μ) k t
      (productANOVATensor μ k base (fun x => rho x * F x)) z ≤ C) :
    finiteWeightedLp (fun x => (FiniteProbabilityWeights.pi μ).weight x * rho x) (q : ℝ)
      (productANOVATruncation μ (Finset.univ.powersetCard k) (fun x => rho x * F x)) ≤
        ((q * k : ℕ) : ℝ) ^ k * C + 1 := by
  sorry

end Erdos3
end
end OAI
