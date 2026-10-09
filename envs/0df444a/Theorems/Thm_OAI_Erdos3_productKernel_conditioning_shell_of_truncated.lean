-- Prove2me | Theorems.Thm_OAI_Erdos3_productKernel_conditioning_shell_of_truncated
-- name    : OAI.Erdos3.productKernel_conditioning_shell_of_truncated
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T14:02:10.281683+00:00
-- url     : https://prove2.me/theorems/f1ffcd98-1aff-4d72-ba48-bcf12f536b73
-- title:
--   Conditioning a low-degree coupled pairing on a fiber costs only a shell error
-- statement:
--   Let $\iota$ be a finite type with decidable equality, and for each $i\in\iota$ let $X_i,Y_i$ be finite types with `FiniteProbabilityWeights` $\mu_i$ on $X_i$ and $\nu_i$ on $Y_i$, and a Markov kernel $K_i\colon X_i\to$ `FiniteProbabilityWeights (Y i)`. Let $C\colon\iota\to\mathbb R$ with $C_i\ge0$, and assume (`hbound`) that for every $i$ and every $f\colon Y_i\to\mathbb R$ with $\nu_i$-mean $0$, $\mathbb E_{\mu_i}\big[(K_if)^2\big]\le C_i\,\mathbb E_{\nu_i}[f^2]$, where $(K_if)(x)$ is the $K_i(x)$-mean of $f$; and (`hK`) that $\mathbb E_{\mu_i}[K_if]=\mathbb E_{\nu_i}f$ for every $i$ and $f$. Let $I\subseteq\iota$ be finite and $b\in\mathbb N$ with $|I|\le b$, reals $\kappa,M,N$ with $0\le\kappa\le1$ and $C_i\le\kappa^2$ for all $i\notin I$, points $x\in\prod X_i$, $y\in\prod Y_i$, and functions $w\colon\prod X_i\to\mathbb R$, $f\colon\prod Y_i\to\mathbb R$. For $S\subseteq\iota$ and a function $g$ write $g_S$ for `productANOVA` (the ANOVA component $\sum_{U\subseteq S}(-1)^{|U|}\mathbb E_{S\setminus U}g$ under the relevant product law), `productANOVAEnergy μ D g` $=\sum_{S\in D}\mathbb E[g_S^2]$ and `productANOVATruncation μ D g` $=\sum_{S\in D}g_S$; let $\mathcal L_b=$ `lowDegreeCoordinateSets ι b` (all $S$ with $|S|\le b$) and $\mathcal C=$ `conditioningCoreSupports I b` (all $S\subseteq\iota\setminus I$ with $|S|\le b-|I|$). Let $\bar w=$ `productSectionAverage μ I I x w`, which with both index sets equal to $I$ is the function sending $z$ to the value of $w$ at the point equal to $x$ on $I$ and to $z$ off $I$, and likewise $\bar f=$ `productSectionAverage ν I I y f`. Assume $\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal L_b\ \bar w}\le M$ and $\sqrt{\texttt{productANOVAEnergy}\ \nu\ \mathcal L_b\ \bar f}\le N$. Let $c_i=$ `FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)`, the coupling of $\mu_i$ and $\nu_i$ whose law is $\mu_i(x')K_i(x')(y')$. Then
--   $$\Big|\langle T_{\mathcal L_b}(\mathbf 1_{I,x}\,w),\,T_{\mathcal L_b}(\mathbf 1_{I,y}\,f)\rangle_c-m_c(I,x,y)\,\langle T_{\mathcal C}\bar w,\,T_{\mathcal C}\bar f\rangle_c\Big|\le 2^{|I|}\,\kappa^{\,b-|I|}\,M\,N,$$
--   where $T_D$ is `productANOVATruncation` over $D$ (for $\mu$ on the left factor and $\nu$ on the right), $\mathbf 1_{I,x}(z)$ is `productFiberIndicator I x z` ($1$ if $z_i=x_i$ for all $i\in I$, else $0$), $\langle F,G\rangle_c=$ `productCouplingPairing c F G` is the mean of $F(z_1)G(z_2)$ under the product of the couplings $c_i$, $m_c(I,x,y)=$ `productCouplingAtomMass c I x y` is the product-coupling probability that $(z_1)_i=x_i$ and $(z_2)_i=y_i$ for all $i\in I$, and $b-|I|$ is a natural-number subtraction.
--
--   Lean: `OAI.Erdos3.productKernel_conditioning_shell_of_truncated` in `lean/OAI/Combinatorics/Progressions/Linear/KernelCoreComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B088` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/KernelCoreComparison.lean#L195

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B088

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
  (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
  (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
    (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
  (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)

include hC hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_conditioning_shell_of_truncated {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) (b : ℕ) (hIb : I.card ≤ b)
    {κ M N : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b) (productSectionAverage μ I I x w)) ≤ M)
    (hf : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) (productSectionAverage ν I I y f)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productCouplingPairing c
      (productANOVATruncation μ (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I x z * w z))
      (productANOVATruncation ν (lowDegreeCoordinateSets ι b) (fun z => productFiberIndicator I y z * f z)) -
      productCouplingAtomMass c I x y * productCouplingPairing c
        (productANOVATruncation μ (conditioningCoreSupports I b) (productSectionAverage μ I I x w))
        (productANOVATruncation ν (conditioningCoreSupports I b) (productSectionAverage ν I I y f))| ≤
      (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) := by
  sorry

end Erdos3
end
end OAI
