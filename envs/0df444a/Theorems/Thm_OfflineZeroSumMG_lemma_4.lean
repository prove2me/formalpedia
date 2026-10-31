-- Prove2me | Theorems.Thm_OfflineZeroSumMG_lemma_4
-- name    : OfflineZeroSumMG.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:48.412931+00:00
-- url     : https://prove2.me/theorems/ff3cc0cb-a9e6-4fbc-b8e7-700c7deb5549
-- title:
--   Lemma 4 — $V^-_{\mathsf{pe}}\ge r^{\mu^\star,\nu_0}+\gamma P^{\mu^\star,\nu_0}V^-_{\mathsf{pe}}-2\beta^{\mu^\star,\nu_0}$
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   Let $\mu^\star$ be a stationary policy of the max-player. For a deterministic $f:\mathcal S\to\mathcal B$ with
--   $$f(s)\in\arg\min_{b\in\mathcal B}\sum_a\mu^\star(a\mid s)Q^-_{\mathsf{pe}}(s,a,b)\quad\text{for all }s,$$
--   let $\nu_0=1_{f}$ (a minimizer in (B.13)), and let $r^{\mu^\star,\nu_0}$, $\beta^{\mu^\star,\nu_0}$ (with $V=V^-_{\mathsf{pe}}$) and $P^{\mu^\star,\nu_0}$ be as in (B.15a)–(B.15c). There is $C_0>0$ such that for every $C_{\mathsf b}\ge C_0$, every game, $1/2\le\gamma<1$, $d_{\mathsf b}$, $\delta\in(0,1)$ and $N\ge1$: with probability exceeding $1-\delta$, for every such $f$,
--   $$V^-_{\mathsf{pe}}\ge r^{\mu^\star,\nu_0}+\gamma P^{\mu^\star,\nu_0}V^-_{\mathsf{pe}}-2\beta^{\mu^\star,\nu_0}.\qquad\text{(B.16)}$$
--
--   This one-step inequality feeds the self-bounding argument (B.17)–(B.21).
--
--   Differences from the source:
--   - reading: a "sufficiently large constant $C_{\mathsf b}>0$" in the algorithm → $\exists C_0>0,\ \forall C_{\mathsf b}\ge C_0$, quantified before every instance quantity; reason: $C_{\mathsf b}$ is a universal constant of the algorithm; $\forall C_{\mathsf b}\ge C_0$ is the stronger reading
--   - reading: $\nu_0$ of (B.13), and (B.14)'s "for instance" $b_s=\arg\max_b\langle\mu^\star(s),Q^-_{\mathsf{pe}}(s,\cdot,b)\rangle$ → $\nu_0=1_{f(s)}$ with $f(s)\in\arg\min_b\sum_a\mu^\star(a|s)Q^-_{\mathsf{pe}}(s,a,b)$; reason: (B.13) defines $\nu_0(s)$ as a minimizer; the arg max of (B.14) is not one (a typo, R2), and the proof (C.39) uses the minimizer
--   - generalization: one deterministic minimizer $\nu_0$ chosen by the proof → every deterministic minimizer $f$, inside the event; reason: implies the statement for the chosen $\nu_0$
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $V^{\mu,\nu}$, $Q^{\mu,\nu}$ as expected discounted sums; $V^{\mu,\star}=\min_\nu$, $V^{\star,\nu}=\max_\mu$; $V(\rho)=\mathbb E_{s\sim\rho}V(s)$ → $V^{\mu,\nu}(s)=\sum_t\gamma^t((P^{\mu,\nu})^t r^{\mu,\nu})(s)$, $Q^{\mu,\nu}$ by its first-step decomposition, best responses as real `⨅`/`⨆` over stationary randomized policies, $V(\rho)=\sum_s\rho(s)V(s)$; reason: the law of $s_t$ is the $t$-th matrix power; the families are nonempty and bounded in $[0,1/(1-\gamma)]$ and the extrema are attained (Appendix A)
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - encoding: probability over the dataset drawn as in (2.4) → `dataProb`: the finite sum over datasets $D:\{1,\dots,N\}\to\mathcal S\times\mathcal A\times\mathcal B\times\mathcal S$ of $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$; reason: this is the law (2.4) on a finite sample space
--   - reading: no condition on $\gamma$ beyond $\gamma\in(0,1)$ in the item itself → $1/2\le\gamma<1$; reason: Appendix B proves Theorem 3, whose standing hypothesis is $1/2\le\gamma<1$ (p.13); the item is a step of that proof
--   - generalization: $\mu^\star$ the max-player part of the Nash equilibrium → any stationary policy $\mu^\star$; reason: the proof never uses the equilibrium property; it specializes to the Nash $\mu^\star$
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), (B.13), p.16; (B.15a)–(B.15c), Lemma 4, (B.16), p.17 (proof: Appendix C.5)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- Lemma 4 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.17): with probability exceeding `1 − δ`,
`V⁻_pe ≥ r^{µ⋆,ν₀} + γ P^{µ⋆,ν₀} V⁻_pe − 2 β^{µ⋆,ν₀}` (B.16), where `ν₀` is a deterministic
policy with `ν₀(s) ∈ arg min_{ν(s) ∈ Δ(B)} E_{a∼µ⋆(s), b∼ν(s)}[Q⁻_pe(s, a, b)]` (B.13) and
`r^{µ⋆,ν₀}`, `β^{µ⋆,ν₀}`, `P^{µ⋆,ν₀}` are (B.15a)–(B.15c).

**Formalization Note.** A deterministic `ν₀` is `purePolicy f` for `f : S → B`; it minimizes the
linear function over `Δ(B)` exactly when `f(s)` minimizes `b ↦ ∑_a µ⋆(a|s) Q⁻_pe(s, a, b)`. The
event holds for every such `f`. The proof never uses that `µ⋆` is an equilibrium strategy, and
the statement holds for every stationary policy `µ⋆`. -/
theorem lemma_4 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cb : ℝ, C₀ ≤ Cb →
    ∀ (S A B : ℕ), 0 < S → 0 < A → 0 < B →
    ∀ (P : Kernel S A B) (r : Reward S A B), IsGame P r →
    ∀ γ : ℝ, 1 / 2 ≤ γ → γ < 1 →
    ∀ db : Fin S → Fin A → Fin B → ℝ, IsDist db →
    ∀ μs : Policy S A,
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ N : ℕ, 1 ≤ N →
      1 - δ < dataProb db P N (fun D =>
        ∀ f : Fin S → Fin B,
          (∀ s (b' : Fin B), ∑ a, (μs s : Fin A → ℝ) a * QpeMinus r γ Cb δ D s a (f s) ≤
                              ∑ a, (μs s : Fin A → ℝ) a * QpeMinus r γ Cb δ D s a b') →
          ∀ s, rPol r μs (purePolicy f) s +
                γ * ∑ s', PPol P μs (purePolicy f) s s' * VpeMinus r γ Cb δ D s' -
                2 * betaPol γ Cb δ D μs (purePolicy f) (VpeMinus r γ Cb δ D) s ≤
              VpeMinus r γ Cb δ D s) := by sorry

end OfflineZeroSumMG
