-- Prove2me | Theorems.Thm_OAI_Erdos3_CylinderRemovalChain_kernel_total_pairing_le
-- name    : OAI.Erdos3.CylinderRemovalChain.kernel_total_pairing_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T17:43:44.310289+00:00
-- url     : https://prove2.me/theorems/035a4d59-89ad-44b3-9b11-97822d8b166f
-- title:
--   Upper bound for the coupled low-degree pairing along a cylinder removal chain
-- statement:
--   Let $\Omega,\iota$ be finite types ($\iota$ with decidable equality), and for $i\in\iota$ let $X_i$ (with decidable equality) and $Y_i$ be finite types with `FiniteProbabilityWeights` $\mu_i$ on $X_i$, all weights positive, and $\nu_i$ on $Y_i$, and Markov kernels $K_i\colon X_i\to$ `FiniteProbabilityWeights (Y i)`. Let $C\colon\iota\to\mathbb R$, $C_i\ge0$, with (`hbound`) $\mathbb E_{\mu_i}[(K_if)^2]\le C_i\,\mathbb E_{\nu_i}[f^2]$ for every $f\colon Y_i\to\mathbb R$ of $\nu_i$-mean $0$, where $(K_if)(x)$ is the $K_i(x)$-mean of $f$, and (`hK`) $\mathbb E_{\mu_i}[K_if]=\mathbb E_{\nu_i}f$ for all $f$. Let $\mathrm{base}\in\prod X_i$, $\mathrm{baseY}\in\prod Y_i$, $p$ `FiniteProbabilityWeights` on $\Omega$, $F\colon\Omega\to\prod X_i$, reals $L,\tau$, naturals $j,r,b$, $w,\mathrm{rem}\colon\Omega\to\mathbb R$ and a list $cs$ of `ProductCylinder X` (a cylinder $c$ is a finite $S_c\subseteq\iota$ with values on $S_c$), with `CylinderRemovalChain μ base p F L τ j r w rem cs` (an inductive predicate: each successive cylinder has $|S_c|\le j$, mass above $\tau$ for the current observed density and `ProductBoundedMarginals` with constants $L,r$ for its normalized section, and the chain passes from $w$ to $\mathrm{rem}$ by erasing the weight on each cylinder in turn), $w\le1$, $0\le\mathrm{rem}\le1$ and $\mathbb E_p\,\mathrm{rem}\le\tau$. Here `observedProductDensity μ p F f` is $y\mapsto\sum_{F(z)=y}p(z)f(z)/\pi(y)$ for $\pi=\prod\mu_i$, and the `mass` of a cylinder $c$ for a function $W$ is the conditional mean $\mathbb E_{S_c}W$ at the point $x_c$ equal to $c$ on $S_c$ and to base elsewhere (`c.assignment base`). Let $\kappa,A,B,M,N,v,\lambda,\varepsilon,\xi,P,Q,\eta,\mathrm{shell},H,G$ be reals with $M,N,v\ge0$, $\tau>0$, $\lambda>0$, $\varepsilon\ge0$, $0<\xi\le1$, $\xi(2+\varepsilon)\le\varepsilon$, $0\le\kappa\le\frac12$, $C_i\le\kappa^2$ for all $i$, $\kappa A^2B^2\le\xi/16$, $MN\le e^P$, `CyclicCrootSisask.spectralIterations ξ P` $\le r$, $j+r\le b$, $\eta\ge0$, `ProductMarginalsClose μ (observedProductDensity μ p F 1) η (2b)` (conditional means over at most $2b$ coordinates within $\eta$ of $1$ at points of positive weight), and $2\eta\,|\mathcal L_b|^2\,4^b(1+\eta)^2\le\tau$, where $\mathcal L_b=$ `lowDegreeCoordinateSets ι b` is the family of subsets of size at most $b$. Let $h,g\colon\prod Y_i\to\mathbb R$ with $\sqrt{\mathcal E_\nu(\mathcal L_b,h)}\le H$ and $\sqrt{\mathcal E_\nu(\mathcal L_b,g)}\le G$, where $\mathcal E(D,\cdot)=$ `productANOVAEnergy … D ·` is the sum over $S\in D$ of the mean square of the ANOVA component on $S$. Let $\mathrm{shell}>0$ with $j+$ `spectralIterations shell Q` $\le b$. Assume (`hbudget`) that the sum, over the pairs $(c,f)$ of $cs$ zipped with `removedCylinderWeights F w cs` (the erased parts of the weight), of $\big|\prod_{i\in S_c}Y_i\big|\cdot m_c\,\lambda(v+\tau)(6+2\varepsilon)\,2^{|S_c|}MN$ is at most $e^Q$, where $m_c$ is the mass of $W_c=$ `observedProductDensity μ p F f` at $c$. Assume (`hpieces`) that for each such pair, with $\sigma^\mu_c(W)(z)$ the value of $W$ at the point equal to $x_c$ on $S_c$ and $z$ off $S_c$ (`productSectionAverage μ S S x W`): $\sqrt{\mathcal E_\mu(\{|S|=k\},m_c^{-1}\sigma^\mu_c(W_c))}\le A^{2k}$ for $1\le k\le r$; $\sqrt{\mathcal E_\mu(\mathcal L_b,m_c^{-1}\sigma^\mu_c(W_c))}\le M$; and for every $z\in\prod_{i\in S_c}Y_i$, with $y$ equal to $z$ on $S_c$ and baseY elsewhere and $\sigma^\nu_y$ defined likewise: $\mathbb E^\nu_{S_c}h(y)\le\lambda\,\mathbb E^\nu_{S_c}g(y)+\lambda\tau$, $v-\tau\le\mathbb E^\nu_{S_c}g(y)$, for $1\le k\le r$ both $\sqrt{\mathcal E_\nu(\{|S|=k\},(4\lambda(v+\tau))^{-1}\sigma^\nu_y h)}\le B^{2k}$ and $\sqrt{\mathcal E_\nu(\{|S|=k\},(2(v+\tau))^{-1}\sigma^\nu_y g)}\le B^{2k}$, and the same two functions have $\sqrt{\mathcal E_\nu(\mathcal L_b,\cdot)}\le N$. Then, with $c_i=$ `FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)` (the coupling with law $\mu_i(x)K_i(x)(y)$),
--   $$\texttt{productTruncatedPairing}\ c\ \mathcal L_b\ (\texttt{observedProductDensity}\ \mu\ p\ F\ w)\ (h-(1+\varepsilon)\lambda g)\le\lambda(1+2\varepsilon)\tau+\frac{\mathrm{shell}}{16}+\sqrt{3\tau}\,\big(H+(1+\varepsilon)\lambda G\big),$$
--   where `productTruncatedPairing c D W f` is the mean, under the product of the couplings, of $T^\mu_DW(z_1)\cdot T^\nu_Df(z_2)$, with $T_D$ = `productANOVATruncation` (the sum of the ANOVA components over $S\in D$).
--
--   Lean: `OAI.Erdos3.CylinderRemovalChain.kernel_total_pairing_le` in `lean/OAI/Combinatorics/Progressions/Linear/KernelCylinderTotal.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B090` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/KernelCylinderTotal.lean#L95

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem CylinderRemovalChain.kernel_total_pairing_le {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {L τ : ℝ} {j r b : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F L τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1) (hmass : p.mean rem ≤ τ)
    {κ A B M N v lam ε ξ P Q η shell H G : ℝ}
    (hM0 : 0 ≤ M) (hN0 : 0 ≤ N) (hv : 0 ≤ v) (hτ : 0 < τ) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hsmall : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hlow : κ * A ^ 2 * B ^ 2 ≤ ξ / 16) (hMN : M * N ≤ Real.exp P)
    (hrtail : CyclicCrootSisask.spectralIterations ξ P ≤ r) (hrb : j + r ≤ b)
    (hη : 0 ≤ η)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) g) ≤ G)
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell Q ≤ b)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, Y i) : ℝ) *
        (cf.1.mass μ base (observedProductDensity μ p F cf.2) * lam * (v + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * M * N))).sum ≤ Real.exp Q)
    (hpieces : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      let m := cf.1.mass μ base (observedProductDensity μ p F cf.2)
      let x := cf.1.assignment base
      let W := observedProductDensity μ p F cf.2
      (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (fun z => m⁻¹ * productSectionAverage μ cf.1.1 cf.1.1 x W z)) ≤ A ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
        (fun z => m⁻¹ * productSectionAverage μ cf.1.1 cf.1.1 x W z)) ≤ M ∧
      ∀ z : ∀ i : cf.1.1, Y i,
        let y := productSubtypePoint cf.1.1 z baseY
        productConditionalMean ν cf.1.1 h y ≤ lam * productConditionalMean ν cf.1.1 g y + lam * τ ∧
        v - τ ≤ productConditionalMean ν cf.1.1 g y ∧
        (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
          (fun a => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y h a)) ≤ B ^ (2 * k)) ∧
        (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
          (fun a => (2 * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y g a)) ≤ B ^ (2 * k)) ∧
        Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
          (fun a => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y h a)) ≤ N ∧
        Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
          (fun a => (2 * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y g a)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets ι b) (observedProductDensity μ p F w)
      (fun z => h z - (1 + ε) * lam * g z) ≤
      lam * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (H + (1 + ε) * lam * G) := by
  sorry

end Erdos3
end
end OAI
