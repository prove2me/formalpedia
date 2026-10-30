-- Prove2me | Theorems.Thm_InfoBargaining_SellerPayoff_corollary_1_i_threshold_theta
-- name    : InfoBargaining.SellerPayoff.corollary_1_i_threshold_theta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:22:21.408265+00:00
-- url     : https://prove2.me/theorems/85d5f104-1b5c-489e-9052-a94f5b02d198
-- title:
--   Corollary 1 (i): maximal information iff $\theta_b>\tilde\theta\in(0,1]$
-- statement:
--   A seller and a buyer may trade one unit. Trade costs the seller $c>0$ and is worth $u$ to the buyer, who does not know $u$; the prior law of $u$ is $F$ with mean $\hat u>0$. Before negotiating, the buyer buys a truth-or-noise signal of informativeness $\alpha\in[\underline\alpha,\bar\alpha]\subseteq(0,1)$; its posterior mean is $v=\alpha w+(1-\alpha)\hat u$, whose law is $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$. The parties then split the net surplus $v-c$ in proportion to their bargaining powers $\theta_s,\theta_b\in(0,1)$, $\theta_s+\theta_b=1$.
--
--   Let $P$ be any of the four focal priors, $0<\underline\alpha<\bar\alpha<1$, $\bar k>0$, the cost linear, and $c$ an admissible cost. Write $\Delta A=A(\bar\alpha,c)-A(\underline\alpha,c)$. There is $\tilde\theta\in(0,1]$ such that for every $\theta_b\in(0,1)$
--
--   $$
--   \alpha^*=\begin{cases}\underline\alpha, & \theta_b\le\tilde\theta,\\ \bar\alpha, & \theta_b>\tilde\theta,\end{cases}
--   $$
--
--   and moreover $\tilde\theta=\bar k/\Delta A$ when $\bar k<\Delta A$, while $\tilde\theta=1$ when $\Delta A\le\bar k$.
--
--   A buyer with little bargaining power cannot recoup the cost of information and stays minimally informed.
--
--   Differences from the source:
--   - reading: α∗, the solution to (6) → optimalInfo, the least maximizer of (6) on [α̲, ᾱ]; reason: (6) can have ties (uniform prior, c = 1/2: A(α, 1/2) = α/8); Corollary 1 sends every tie to α̲
--   - reading: θ̃ ≡ k̄/[A(ᾱ, c) − A(α̲, c)] (proof, p. 30) together with θ̃ ∈ (0, 1] (Corollary 1) → θ̃ = k̄/ΔA when k̄ < ΔA, θ̃ = 1 when ΔA ≤ k̄; reason: the proof's ratio may exceed 1 or divide by zero; min{1, k̄/ΔA} (1 when ΔA = 0) is the value in (0, 1] that makes the corollary true
--   - reading: θ_s, θ_b ∈ (0, 1), θ_s + θ_b = 1 (p. 7); [α̲, ᾱ] ⊆ (0, 1), k̄ = k(ᾱ) > 0 = k(α̲) (p. 8); c > 0 (p. 6), c ∈ (u̲, ū) (p. 7) → explicit hypotheses 0 < α̲ < ᾱ < 1, 0 < k̄, θ ∈ (0, 1), c ∈ P.costDomain, θ_b = 1 − θ_s; reason: the section's standing assumptions; α̲ < ᾱ because k(α̲) = 0 < k̄ = k(ᾱ) and the linear k divides by ᾱ − α̲
--   - encoding: A(α, c) = ∫_c^v̄ (v − c) dG(v, α) with G(v, α) = F((v − (1 − α)û)/α) → totalSurplus μ α c = ∫ max(v − c, 0) d(postMeanLaw μ α), postMeanLaw the image of the prior under u ↦ αu + (1 − α)·priorMean μ; reason: the same quantity: G(·, α) is the CDF of that image law and (v − c)⁺ vanishes below c
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), Corollary 1 (i), p. 13; threshold θ̃ ≡ k̄/[A(ᾱ, c) − A(α̲, c)] from its proof, p. 30

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_costDomain
import Definitions.Def_InfoBargaining_SellerPayoff_optimalInfo

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **Corollary 1 (i): maximal information exactly when the buyer's power exceeds `θ̃ ∈ (0, 1]`.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022), Corollary 1 (i), p. 13: "Consider either of the four focal distributions. (i) There exists
a θ̃ ∈ (0, 1] such that the optimal level of buyer information acquisition is: α∗ = α̲ for
θ_b ≤ θ̃, and α∗ = ᾱ for θ_b > θ̃"; the proof (p. 30) gives "θ̃ ≡ k̄/[A(ᾱ, c) − A(α̲, c)]".

For every focal prior, every `0 < α̲ < ᾱ < 1`, `k̄ > 0` and every admissible cost `c`, with
`ΔA = A(ᾱ, c) − A(α̲, c)`, there is `θ̃ ∈ (0, 1]` such that for every `θ_b ∈ (0, 1)`,
`α* = α̲` if `θ_b ≤ θ̃` and `α* = ᾱ` otherwise; moreover `θ̃ = k̄/ΔA` when `k̄ < ΔA` and
`θ̃ = 1` when `ΔA ≤ k̄`.

**Formalization Note.** The proof's `θ̃ ≡ k̄/ΔA` may exceed `1` or divide by zero; with the
corollary's `θ̃ ∈ (0, 1]` it is read as `min{1, k̄/ΔA}` (`1` when `ΔA = 0`). `α*` is the least
maximizer of (6). -/
theorem corollary_1_i_threshold_theta (P : FocalPrior) (αl αh kbar c : ℝ)
    (hαl : 0 < αl) (hαlh : αl < αh) (hαh : αh < 1) (hk : 0 < kbar)
    (hc : c ∈ P.costDomain) :
    ∃ θt : ℝ, 0 < θt ∧ θt ≤ 1 ∧
      (∀ θb ∈ Set.Ioo (0:ℝ) 1,
        optimalInfo P.measure αl αh kbar θb c = if θb ≤ θt then αl else αh) ∧
      (kbar < totalSurplus P.measure αh c - totalSurplus P.measure αl c →
        θt = kbar / (totalSurplus P.measure αh c - totalSurplus P.measure αl c)) ∧
      (totalSurplus P.measure αh c - totalSurplus P.measure αl c ≤ kbar → θt = 1) := by sorry

end InfoBargaining.SellerPayoff
