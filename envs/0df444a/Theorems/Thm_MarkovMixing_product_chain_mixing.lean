-- Prove2me | Theorems.Thm_MarkovMixing_product_chain_mixing
-- name    : MarkovMixing.product_chain_mixing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:40:10.467132+00:00
-- url     : https://prove2.me/theorems/6a5c4946-286f-47f0-b73e-b888f9d9811c
-- title:
--   Product chains mix at time $\frac{n\log n}{2\gamma}$
-- statement:
--   For $i=1,\dots,n$ let $P_i$ be an **irreducible**, reversible Markov chain on a finite space $W_i$ of at least two states, with stationary distribution $\pi_i$ (detailed balance $\pi_i(x)P_i(x,y)=\pi_i(y)P_i(y,x)$). The **product chain** on $W_1\times\cdots\times W_n$ picks a uniformly random coordinate and updates it by its own chain, $P=\tfrac1n\sum_i\widetilde P_i$; its stationary distribution is the product $\pi(x)=\prod_i\pi_i(x_i)$. Mixing is measured in continuous time: with the heat kernel $H_t=\sum_ke^{-t}\tfrac{t^k}{k!}P^k$ and the total variation distance $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$, the **continuous mixing time** $t^{\mathrm{cont}}_{\mathrm{mix}}(\varepsilon)$ is the first real time at which $\max_x\|H_t(x,\cdot)-\pi\|_{TV}\le\varepsilon$. Each factor's **spectral gap** is $\gamma_i=1-\lambda_2(P_i)$, with $\lambda_2$ the largest eigenvalue $\ne1$ (Mission VII); irreducibility together with at least two states is what makes this the book's $\gamma_i$.
--
--   The theorem (Theorem 20.7 of Levin–Peres–Wilmer) asserts, for $0<\varepsilon<1$, $n\ge2$:
--
--   1. if every $\gamma_i\ge\gamma$ and every factor satisfies $\sqrt{\min_x\pi_i(x)}\ge c_0$, then $\displaystyle t^{\mathrm{cont}}_{\mathrm{mix}}(\varepsilon)\le\frac{n\log n}{2\gamma}+\frac n\gamma\log\frac{1}{c_0\varepsilon}$;
--   2. if moreover $\gamma_i=\gamma$ exactly for every $i$, then $\displaystyle t^{\mathrm{cont}}_{\mathrm{mix}}(\varepsilon)\ge\frac{n}{2\gamma}\Bigl(\log n-\log\bigl(8\log\tfrac1{1-\varepsilon}\bigr)\Bigr)$.
--
--   The product of $n$ independent chains mixes at time $\tfrac{n\log n}{2\gamma}$, not $\tfrac n\gamma$: a coupon-collector logarithm beyond the obvious slowdown, because the *last* coordinate to equilibrate is what matters. This is the abstract form of the hypercube's $\tfrac12n\log n$ (the hypercube is the product of $n$ two-state chains with $\gamma=1$), and the template computation behind the cutoff of Mission XI.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 20.4, Theorem 20.7, Eqs. (20.15)-(20.16), p. 269

import Definitions.Def_mm_continuous
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 20.7** (LPW): mixing of continuous-time product chains.  If
each factor has spectral gap at least `γ` and `√π^{(i)}_min ≥ c₀`, then
`t^{cont}_mix(ε) ≤ (2γ)⁻¹ n log n + γ⁻¹ n log(1/(c₀ε))`; if all gaps equal
`γ`, then also
`t^{cont}_mix(ε) ≥ (n/2γ)(log n − log(8 log(1/(1−ε))))`.

Each factor is hypothesized irreducible and to have at least two states, so
that its `spectralGap` is the book's `γᵢ = 1 − λ₂`. `lambdaTwo` is a supremum
over the eigenvalues different from `1`; for a one-state chain, or the identity
chain, that set is empty and `sSup ∅ = 0` reports a spectral gap of `1` for a
chain that does not mix at all — under which the lower bound (20.16) is
false. -/
theorem product_chain_mixing {n : ℕ} (hn : 2 ≤ n) {W : Fin n → Type*}
    [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)] [∀ i, Nonempty (W i)]
    (P : ∀ i, Matrix (W i) (W i) ℝ) (hP : ∀ i, IsStochastic (P i))
    (hirr : ∀ i, Irreducible (P i)) (hcard : ∀ i, 2 ≤ Fintype.card (W i))
    (π : ∀ i, W i → ℝ) (hπ : ∀ i, IsStationary (P i) (π i))
    (hrev : ∀ i, DetailedBalance (P i) (π i))
    (γ c₀ : ℝ) (hγ : 0 < γ) (hgap : ∀ i, γ ≤ spectralGap (P i))
    (hc0 : 0 < c₀) (hmin : ∀ i, c₀ ≤ Real.sqrt (⨅ x, π i x))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    contMixingTime (productChain P) (fun x => ∏ i, π i (x i)) ε ≤
      (2 * γ)⁻¹ * n * Real.log n + γ⁻¹ * n * Real.log (1 / (c₀ * ε)) ∧
    ((∀ i, spectralGap (P i) = γ) →
      (n : ℝ) / (2 * γ) *
          (Real.log n - Real.log (8 * Real.log (1 / (1 - ε)))) ≤
        contMixingTime (productChain P) (fun x => ∏ i, π i (x i)) ε) := by
  sorry

end MarkovMixing
