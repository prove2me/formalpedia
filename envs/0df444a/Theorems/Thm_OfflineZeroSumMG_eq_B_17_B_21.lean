-- Prove2me | Theorems.Thm_OfflineZeroSumMG_eq_B_17_B_21
-- name    : OfflineZeroSumMG.eq_B_17_B_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:51.467147+00:00
-- url     : https://prove2.me/theorems/ad09009d-e38e-431d-8abc-391395e8786a
-- title:
--   (B.17)–(B.21) — self-bounding: $V^\star(\rho)-V^{\hat\mu,\star}(\rho)\le\frac{2}{1-\gamma}(d^{\mu^\star,\nu_0})^\top\beta^{\mu^\star,\nu_0}$
-- statement:
--   Let $\mathrm{MG}$ be a discounted zero-sum Markov game with rewards in $[0,1]$, $0<\gamma<1$, $\rho\in\Delta(\mathcal S)$, $(\mu^\star,\nu^\star)$ a Nash equilibrium with value $V^\star=V^{\mu^\star,\nu^\star}$, $\hat\mu$ any stationary policy, $\nu_0=1_f$ any deterministic policy of the min-player, and $W,\beta:\mathcal S\to\mathbb R$ vectors with
--   $$W\le V^{\hat\mu,\star}\qquad\text{and}\qquad W\ge r^{\mu^\star,\nu_0}+\gamma P^{\mu^\star,\nu_0}W-2\beta.$$
--   Then
--
--   1. $V^\star=V^{\mu^\star,\star}$ and $V^\star-V^{\hat\mu,\star}\le V^{\mu^\star,\nu_0}-W$ at every state (B.17);
--   2. $\rho^\top(V^{\mu^\star,\nu_0}-W)\le\frac{2}{1-\gamma}(d^{\mu^\star,\nu_0})^\top\beta$ (B.21);
--   3. $V^\star(\rho)-V^{\hat\mu,\star}(\rho)\le\frac{2}{1-\gamma}(d^{\mu^\star,\nu_0})^\top\beta$ (p.18);
--   4. $d^{\mu^\star,\nu_0}=(1-\gamma)\rho^\top\sum_{i\ge0}\gamma^i(P^{\mu^\star,\nu_0})^i=(1-\gamma)\rho^\top(I-\gamma P^{\mu^\star,\nu_0})^{-1}$ (B.20).
--
--   In the paper $W=V^-_{\mathsf{pe}}$ (the first hypothesis is Lemma 3, the second is Lemma 4) and $\beta=\beta^{\mu^\star,\nu_0}$, which reduces the max-player's suboptimality to the occupancy-weighted penalty bounded in Lemma 5.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $V^{\mu,\nu}$, $Q^{\mu,\nu}$ as expected discounted sums; $V^{\mu,\star}=\min_\nu$, $V^{\star,\nu}=\max_\mu$; $V(\rho)=\mathbb E_{s\sim\rho}V(s)$ → $V^{\mu,\nu}(s)=\sum_t\gamma^t((P^{\mu,\nu})^t r^{\mu,\nu})(s)$, $Q^{\mu,\nu}$ by its first-step decomposition, best responses as real `⨅`/`⨆` over stationary randomized policies, $V(\rho)=\sum_s\rho(s)V(s)$; reason: the law of $s_t$ is the $t$-th matrix power; the families are nonempty and bounded in $[0,1/(1-\gamma)]$ and the extrema are attained (Appendix A)
--   - encoding: $d^{\mu,\nu}(s,a,b;\rho)$ of (2.2) → $d^{\mu,\nu}(s;\rho)\mu(a|s)\nu(b|s)$ with $d^{\mu,\nu}(s;\rho)=(1-\gamma)\sum_t\gamma^t(\rho^\top(P^{\mu,\nu})^t)(s)$; reason: this is (2.3), which the paper derives from (2.2)
--   - generalization: the standing $1/2\le\gamma<1$ of Theorem 3 (p.13) → $0<\gamma<1$, the range of the game (§2.1, p.4); reason: the item's own sentence has no condition on $\gamma$ and the statement holds on the whole range; it specializes to $\gamma\ge1/2$
--   - generalization: $V^-_{\mathsf{pe}}$, $\beta^{\mu^\star,\nu_0}$ and the minimizer $\nu_0$ of (B.13), with the hypotheses supplied by Lemmas 3 and 4 → arbitrary vectors $W$, $\beta$ satisfying $W\le V^{\hat\mu,\star}$ and (B.16), and any deterministic $\nu_0$; reason: a deterministic statement whose instance $W=V^-_{\mathsf{pe}}$, $\beta=\beta^{\mu^\star,\nu_0}$ is the paper's
--   - encoding: $(I-\gamma P^{\mu^\star,\nu_0})^{-1}$ → Mathlib's matrix inverse `(1 - γ • P)⁻¹`; reason: the matrix is invertible for $\gamma<1$, so `⁻¹` is the true inverse
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), (B.17)–(B.21), p.17, and the display on p.18

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

open Matrix

namespace OfflineZeroSumMG

/-- (B.17)–(B.21) (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.17, with the conclusion on p.18):
the self-bounding step. If `V⁻_pe ≤ V^{µ̂,⋆}` (Lemma 3) and
`V⁻_pe ≥ r^{µ⋆,ν₀} + γ P^{µ⋆,ν₀} V⁻_pe − 2 β^{µ⋆,ν₀}` (B.16), then

* (B.17) `V⋆ = V^{µ⋆,⋆}` and `V⋆ − V^{µ̂,⋆} ≤ V^{µ⋆,ν₀} − V⁻_pe` at every state;
* (B.21) `ρ⊤(V^{µ⋆,ν₀} − V⁻_pe) ≤ (2/(1−γ)) (d^{µ⋆,ν₀})⊤ β^{µ⋆,ν₀}`;
* (p.18) `V⋆(ρ) − V^{µ̂,⋆}(ρ) ≤ (2/(1−γ)) (d^{µ⋆,ν₀})⊤ β^{µ⋆,ν₀}`;
* (B.20) `d^{µ⋆,ν₀} = (1 − γ) ρ⊤ (I − γ P^{µ⋆,ν₀})^{−1}`,

where `d^{µ⋆,ν₀} = (1 − γ) ρ⊤ ∑_i γ^i (P^{µ⋆,ν₀})^i` is the occupancy (2.1).

**Formalization Note.** Deterministic: `V⁻_pe` and `β^{µ⋆,ν₀}` are replaced by arbitrary vectors
`W` and `β` satisfying the two hypotheses, and `ν₀` by an arbitrary deterministic policy
`purePolicy f`; the paper's instance is `W = V⁻_pe`, `β = β^{µ⋆,ν₀}`. Stated for the whole range
`0 < γ < 1` of the game (§2.1, p.4). `(µ⋆, ν⋆)` is a Nash
equilibrium with `V⋆ = V^{µ⋆,ν⋆}`; `µ̂` is any stationary policy. `(I − γP)^{−1}` is Mathlib's
matrix inverse `⁻¹`. -/
theorem eq_B_17_B_21 {S A B : ℕ} (hS : 0 < S) (hA : 0 < A) (hB : 0 < B)
    (P : Kernel S A B) (r : Reward S A B) (hG : IsGame P r)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (ρ : Fin S → ℝ) (hρ : ρ ∈ stdSimplex ℝ (Fin S))
    (μs : Policy S A) (νs : Policy S B) (hNE : IsNash P r γ μs νs)
    (μh : Policy S A) (f : Fin S → Fin B) (W β : Fin S → ℝ)
    (hW : ∀ s, W s ≤ VminBR P r γ μh s)
    (hB16 : ∀ s, rPol r μs (purePolicy f) s +
        γ * ∑ s', PPol P μs (purePolicy f) s s' * W s' - 2 * β s ≤ W s) :
    (∀ s, V P r γ μs νs s = VminBR P r γ μs s) ∧
    (∀ s, V P r γ μs νs s - VminBR P r γ μh s ≤ V P r γ μs (purePolicy f) s - W s) ∧
    atDist ρ (V P r γ μs (purePolicy f)) - atDist ρ W ≤
        2 / (1 - γ) * ∑ s, occState P γ ρ μs (purePolicy f) s * β s ∧
    atDist ρ (V P r γ μs νs) - atDist ρ (VminBR P r γ μh) ≤
        2 / (1 - γ) * ∑ s, occState P γ ρ μs (purePolicy f) s * β s ∧
    (∀ s, occState P γ ρ μs (purePolicy f) s =
        (1 - γ) * (ρ ᵥ* (1 - γ • PPol P μs (purePolicy f))⁻¹) s) := by sorry

end OfflineZeroSumMG
