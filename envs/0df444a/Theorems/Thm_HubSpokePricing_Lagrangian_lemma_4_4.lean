-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_lemma_4_4
-- name    : HubSpokePricing.Lagrangian.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:44.078266+00:00
-- url     : https://prove2.me/theorems/88fe2cde-b6ce-4a02-84e2-f202e0bc9023
-- title:
--   Lemma 4.4, p. 19 — X̃_i(δ) stochastically dominates X_i(δ); X̃₀(δ) is stochastically dominated by X₀(δ)
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   Let $0\le\delta<m$, $\lambda^*(\delta)$ optimal to (11) and $\pi(\delta)$ the Lagrangian policy from optimal solutions $p_i$ of (6). Let $X(\delta)$ be distributed according to a stationary distribution $\mu$ of the original system, and $\tilde X(\delta)$ according to the relaxed system's stationary law $\prod_ip_i(x_i)$ (Corollary B.10); the hub levels are $X_0(\delta)=m-\sum_iX_i(\delta)$ and $\tilde X_0(\delta)=m-\sum_i\tilde X_i(\delta)$, the latter possibly negative. Then
--
--   1. for every spoke $i$ and every $k$, $\;\mathbb P[\tilde X_i(\delta)\le k]\le\mathbb P[X_i(\delta)\le k]$;
--   2. for every integer $k$, $\;\mathbb P[X_0(\delta)\le k]\le\mathbb P[\tilde X_0(\delta)\le k]$.
--
--   That is, each relaxed spoke level first-order stochastically dominates the original one, and the relaxed hub level is first-order stochastically dominated by the original one.
--
--   **Formalization Note** The relaxed system's stationary distribution is written as $\prod_ip_i(x_i)$, which Corollary B.10 identifies as its unique stationary law. Spoke levels are natural numbers (negative $k$ is trivial); the relaxed hub level is computed in $\mathbb Z$.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, p. 19, Lemma 4.4; p. 52, A.9

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Lemma 4.4 (p. 19): under `π(δ)`, each spoke level `X̃ᵢ(δ)` of the relaxed system (stationary
law `∏ᵢ p_i(x_i)`) first-order stochastically dominates the spoke level `Xᵢ(δ)` of the original
system (stationary law `μ`), and the relaxed hub level `X̃₀(δ) = m − ∑ᵢ X̃ᵢ(δ)` (an integer,
possibly negative) is first-order stochastically dominated by the original hub level `X₀(δ)`. -/
theorem lemma_4_4 (N : Network) (hN : N.Standing) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδm : δ < N.m)
    (lam : ℝ) (hlam : IsDualOpt N δ lam)
    (sol : Fin N.n → SpokeSol N.m) (hsol : ∀ i, SpokeOptimal N lam i (sol i))
    (μ : OrigState N → ℝ) (hμ : MarkovChain.IsStationary (origKernel N sol) μ) :
    (∀ (i : Fin N.n) (k : ℕ),
      (∑ x : RelaxState N, if (x i : ℕ) ≤ k then prodLaw N sol x else 0) ≤
        ∑ x : OrigState N, if (x.1 i : ℕ) ≤ k then μ x else 0) ∧
    (∀ k : ℤ,
      (∑ x : OrigState N, if (N.m : ℤ) - ∑ i, ((x.1 i : ℕ) : ℤ) ≤ k then μ x else 0) ≤
        ∑ x : RelaxState N, if (N.m : ℤ) - ∑ i, ((x i : ℕ) : ℤ) ≤ k then prodLaw N sol x else 0) := by sorry

end HubSpokePricing.Lagrangian
