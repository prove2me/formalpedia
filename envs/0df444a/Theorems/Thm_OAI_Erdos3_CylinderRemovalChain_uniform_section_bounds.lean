-- Prove2me | Theorems.Thm_OAI_Erdos3_CylinderRemovalChain_uniform_section_bounds
-- name    : OAI.Erdos3.CylinderRemovalChain.uniform_section_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T15:17:27.009983+00:00
-- url     : https://prove2.me/theorems/6a994be1-fe61-4918-8703-600fc4691299
-- title:
--   Uniform ANOVA energy bounds for the normalized sections of a cylinder removal chain
-- statement:
--   Let $\Omega$ and $\iota$ be finite types, $\iota$ linearly ordered, and for $i\in\iota$ let $X_i$ be a finite type with decidable equality carrying `FiniteProbabilityWeights` $\mu_i$ with every weight positive; let $\mathrm{base}\in\prod_iX_i$, let $p$ be `FiniteProbabilityWeights` on $\Omega$ and $F\colon\Omega\to\prod_iX_i$. For $f\colon\Omega\to\mathbb R$, `observedProductDensity μ p F f` is the function $y\mapsto\sum_{z:F(z)=y}p(z)f(z)\,/\,\pi(y)$ on $\prod_iX_i$, $\pi$ the product of the $\mu_i$. A `ProductCylinder X` is a finite set $S\subseteq\iota$ with values $c_i\in X_i$ for $i\in S$; its `mass` for a function $g$ is the conditional mean $\mathbb E_Sg$ at the point equal to $c$ on $S$ and to base elsewhere, and `ProductCylinder.normalizedSection μ base g c` is the function sending $x$ to $g$ at the point equal to $c$ on $S$ and $x$ off $S$, divided by that mass. `CylinderRemovalChain μ base p F K τ j r w rem cs` is the inductive predicate saying that $\mathrm{rem}=w$ when the list $cs$ is empty, and that for $cs=c::cs'$: $|S_c|\le j$, $\tau<$ the mass of `observedProductDensity μ p F w` at $c$, the corresponding normalized section has `ProductBoundedMarginals` with constants $K,r$ (its conditional means over at most $r$ coordinates, at points of positive $\pi$-weight, are at most $K^{\#\text{coordinates}}$), and the chain continues from $w$ with the $z$ satisfying $F(z)\in c$ erased (weight set to $0$) to $\mathrm{rem}$ along $cs'$. `removedCylinderWeights F w cs` is the list of the erased parts (the weight restricted to $\{z:F(z)\in c\}$ at each step). Let $K,\tau,\eta,P$ be reals and $j,r,q,b$ natural numbers, $w,\mathrm{rem}\colon\Omega\to\mathbb R$ and $cs$ a list of cylinders, with the chain hypothesis `CylinderRemovalChain μ base p F K τ j r w rem cs`, $1\le K$, $0<\tau$, $0\le\eta\le1$, $q\ge2$ even, $r\le P$, $\log(2+\tau^{-1})\le P\le q\le P+2$, $\eta\le\frac12\big((2^{r+1}(2+|\iota|)^r(2+\tau^{-1}))^q\big)^{-1}$, `ProductMarginalsClose μ (observedProductDensity μ p F 1) η (max (j + r(q+1)) (2b + j))` (every conditional mean over at most that many coordinates, at points of positive $\pi$-weight, is within $\eta$ of $1$), $2\eta\,|\mathcal L_b|^2\,4^b(1+\eta)^2\le1$ where $\mathcal L_b=$ `lowDegreeCoordinateSets ι b` is the family of subsets of size at most $b$, and $0\le w\le1$. Then for every pair $(c,f)$ in $cs$ zipped with `removedCylinderWeights F w cs`, writing $g=$ `ProductCylinder.normalizedSection μ base (observedProductDensity μ p F f) c`: for every $k\le r$, $\sqrt{\texttt{productANOVAEnergy}\ \mu\ \{S:|S|=k\}\ g}\le(8(1+K)(P+2))^{2k}$; and $\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal L_b\ g}\le3\tau^{-1}$. Here `productANOVAEnergy μ D g` is $\sum_{S\in D}\mathbb E_\pi[g_S^2]$ for the ANOVA components $g_S=\sum_{U\subseteq S}(-1)^{|U|}\mathbb E_{S\setminus U}g$.
--
--   Lean: `OAI.Erdos3.CylinderRemovalChain.uniform_section_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/CylinderUniformSections.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B094` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/CylinderUniformSections.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B094

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem CylinderRemovalChain.uniform_section_bounds {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [LinearOrder ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ η P : ℝ} {j r q b : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hK : 1 ≤ K) (hτ : 0 < τ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hq : 2 ≤ q) (heven : Even q)
    (hrP : (r : ℝ) ≤ P) (hlog : Real.log (2 + τ⁻¹) ≤ P)
    (hPq : P ≤ (q : ℝ)) (hqP : (q : ℝ) ≤ P + 2)
    (hsmall : η ≤ (1 / 2) * (((2 : ℝ) ^ (r + 1) * (2 + (Fintype.card ι : ℝ)) ^ r * (2 + τ⁻¹)) ^ q)⁻¹)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η
      (max (j + r * (q + 1)) (2 * b + j)))
    (herr : 2 * η * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) :
    ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      (∀ k, k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤
          (8 * (1 + K) * (P + 2)) ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
        (ProductCylinder.normalizedSection μ base (observedProductDensity μ p F cf.2) cf.1)) ≤ 3 * τ⁻¹ := by
  sorry

end Erdos3
end
end OAI
