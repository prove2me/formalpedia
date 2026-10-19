-- Prove2me | Theorems.Thm_OAI_Erdos3_productKernel_scaled_conditioned_mean_comparison_s2
-- name    : OAI.Erdos3.productKernel_scaled_conditioned_mean_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:43.622322+00:00
-- url     : https://prove2.me/theorems/95b1f1cc-8a0b-47de-8841-46e119e3f264
-- title:
--   Low-degree truncated pairing on a coupling atom compared with the product of conditional means, for product kernels
-- statement:
--   Let $\iota$ be a finite type with decidable equality, and for each $i \in \iota$ let $X_i, Y_i$ be finite types, $\mu_i$ and $\nu_i$ `FiniteProbabilityWeights` (probability weight vectors, defined by OpenAI) on $X_i$ and $Y_i$, and $K_i$ a Markov kernel assigning to each $x \in X_i$ probability weights $K_i(x)$ on $Y_i$. Let $C : \iota \to \mathbb{R}$ with $C_i \ge 0$, and suppose for every $i$:
--   - for every $f : Y_i \to \mathbb{R}$ with $\mathbb{E}_{\nu_i} f = 0$: $\ \mathbb{E}_{x \sim \mu_i}\bigl[(\mathbb{E}_{K_i(x)} f)^2\bigr] \le C_i\, \mathbb{E}_{\nu_i}[f^2]$;
--   - for every $f : Y_i \to \mathbb{R}$: $\ \mathbb{E}_{x \sim \mu_i}\bigl[\mathbb{E}_{K_i(x)} f\bigr] = \mathbb{E}_{\nu_i} f$.
--
--   Write $\mu = \prod_i \mu_i$ and $\nu = \prod_i \nu_i$. Let $I \subseteq \iota$ be a finite set and $r, b$ natural numbers with $|I| \le b$ and $r \le b - |I|$. Let $\kappa, A, B, M, N, m, s$ be real numbers with $m > 0$, $s > 0$, $0 \le \kappa \le 1$, $C_i \le \kappa^2$ for every $i \notin I$, and $\kappa A^2 B^2 \le 1/2$. Let $x \in \prod_i X_i$, $y \in \prod_i Y_i$, $w : \prod_i X_i \to \mathbb{R}$ and $f : \prod_i Y_i \to \mathbb{R}$. Write $\tilde w = m^{-1}\cdot$`productSectionAverage μ I I x w` and $\tilde f = s^{-1}\cdot$`productSectionAverage ν I I y f` (section averages defined by OpenAI), write $\mathcal{P}_k$ for the family of subsets of $\iota$ of size $k$, $\mathcal{L}_b$ = `lowDegreeCoordinateSets ι b` for the family of subsets of size at most $b$, and `productANOVAEnergy μ D g` $= \sum_{S \in D} \mathbb{E}_{\mu}[(g_S)^2]$ for the energy of the ANOVA components $g_S$ (`productANOVA`, defined by OpenAI). Suppose:
--   - for every $k$ with $1 \le k \le r$: $\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{P}_k\ \tilde w} \le A^{2k}$ and $\sqrt{\texttt{productANOVAEnergy}\ \nu\ \mathcal{P}_k\ \tilde f} \le B^{2k}$;
--   - $\sqrt{\texttt{productANOVAEnergy}\ \mu\ \mathcal{L}_b\ \tilde w} \le M$ and $\sqrt{\texttt{productANOVAEnergy}\ \nu\ \mathcal{L}_b\ \tilde f} \le N$.
--
--   Let $c_i$ = `FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) _` be the coupling of $\mu_i$ and $\nu_i$ whose law is $x \mapsto \mu_i(x) K_i(x)$ (defined by OpenAI). Let $\Pi$ = `productAtomTruncatedPairing c 𝓛_b I x y w f`, the pairing under the product coupling $\prod_i c_i$ of the $\mathcal{L}_b$-ANOVA truncations of $z \mapsto \mathbf{1}[z_i = x_i\ \forall i \in I]\, w(z)$ and of $z \mapsto \mathbf{1}[z_i = y_i\ \forall i \in I]\, f(z)$; let $\alpha$ = `productCouplingAtomMass c I x y`, the mass that the product coupling gives to pairs agreeing with $(x_i, y_i)$ for all $i \in I$; and let `productConditionalMean μ I w x` be the $\mu$-mean of $w$ over the coordinates outside $I$ with the coordinates in $I$ fixed to those of $x$ (similarly for $\nu, f, y$). Then
--   $$\Bigl| \Pi - \alpha\cdot\bigl(\texttt{productConditionalMean}\ \mu\ I\ w\ x\cdot \texttt{productConditionalMean}\ \nu\ I\ f\ y\bigr) \Bigr| \le m s\Bigl(2^{|I|}\bigl(\kappa^{b - |I|} M N\bigr) + \alpha\bigl(2(\kappa A^2 B^2) + \kappa^{r} M N\bigr)\Bigr).$$
--
--   Lean: `OAI.Erdos3.productKernel_scaled_conditioned_mean_comparison_s2`, which states OpenAI's `OAI.Erdos3.productKernel_scaled_conditioned_mean_comparison` (in `lean/OAI/Combinatorics/Progressions/Estimates/ScaledConditionedComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B150` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ScaledConditionedComparison.lean (declaration OAI.Erdos3.productKernel_scaled_conditioned_mean_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem productKernel_scaled_conditioned_mean_comparison_s2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N m s : ℝ} (hm : 0 < m) (hs : 0 < s)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hsmall : κ * A ^ 2 * B ^ 2 ≤ 1 / 2)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (f : (∀ i, Y i) → ℝ)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ A ^ (2 * k))
    (hf : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ M)
    (hN : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => s⁻¹ * productSectionAverage ν I I y f z)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w f -
      productCouplingAtomMass c I x y *
        (productConditionalMean μ I w x * productConditionalMean ν I f y)| ≤
      m * s * ((2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N) +
        productCouplingAtomMass c I x y * (2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N)) := by
  sorry

end Erdos3

end

end OAI
end
