-- Prove2me | Theorems.Thm_OfflineZeroSumMG_lemma_3
-- name    : OfflineZeroSumMG.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:46.549007+00:00
-- url     : https://prove2.me/theorems/64543033-94f7-4f86-a813-d5ab9feb3571
-- title:
--   Lemma 3 — pessimism: $Q^-_{\mathsf{pe}}\le Q^{\hat\mu,\star}$, $Q^+_{\mathsf{pe}}\ge Q^{\star,\hat\nu}$, $V^-_{\mathsf{pe}}\le V^{\hat\mu,\star}$, $V^+_{\mathsf{pe}}\ge V^{\star,\hat\nu}$
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   There is $C_0>0$ such that for every $C_{\mathsf b}\ge C_0$, every game, $1/2\le\gamma<1$, every $d_{\mathsf b}$, $\delta\in(0,1)$ and $N\ge1$: with probability exceeding $1-\delta$, every policy pair $(\hat\mu,\hat\nu)$ returned by Algorithm 1 satisfies
--   $$Q^-_{\mathsf{pe}}\le Q^{\hat\mu,\star},\qquad Q^+_{\mathsf{pe}}\ge Q^{\star,\hat\nu},\qquad V^-_{\mathsf{pe}}\le V^{\hat\mu,\star},\qquad V^+_{\mathsf{pe}}\ge V^{\star,\hat\nu}.$$
--
--   Here $Q^{\mu,\star}=\min_\nu Q^{\mu,\nu}$ and $Q^{\star,\nu}=\max_\mu Q^{\mu,\nu}$. The pessimistic estimates are thus certified lower (resp. upper) bounds on what the returned policies guarantee against a best response.
--
--   Differences from the source:
--   - reading: a "sufficiently large constant $C_{\mathsf b}>0$" in the algorithm → $\exists C_0>0,\ \forall C_{\mathsf b}\ge C_0$, quantified before every instance quantity; reason: $C_{\mathsf b}$ is a universal constant of the algorithm; $\forall C_{\mathsf b}\ge C_0$ is the stronger reading
--   - generalization: the policy pair returned by Algorithm 1, where MatrixNash returns "a solution" of the matrix game → every pair $(\hat\mu,\hat\nu)$ such that, at every state, $\hat\mu(s)$ is the max-player part of a saddle point of $Q^-_{\mathsf{pe}}(s,\cdot,\cdot)$ and $\hat\nu(s)$ the min-player part of a saddle point of $Q^+_{\mathsf{pe}}(s,\cdot,\cdot)$, inside one event; reason: implies the statement for every selection rule of MatrixNash; saddle points exist by the minimax theorem, so the set is nonempty
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $V^{\mu,\nu}$, $Q^{\mu,\nu}$ as expected discounted sums; $V^{\mu,\star}=\min_\nu$, $V^{\star,\nu}=\max_\mu$; $V(\rho)=\mathbb E_{s\sim\rho}V(s)$ → $V^{\mu,\nu}(s)=\sum_t\gamma^t((P^{\mu,\nu})^t r^{\mu,\nu})(s)$, $Q^{\mu,\nu}$ by its first-step decomposition, best responses as real `⨅`/`⨆` over stationary randomized policies, $V(\rho)=\sum_s\rho(s)V(s)$; reason: the law of $s_t$ is the $t$-th matrix power; the families are nonempty and bounded in $[0,1/(1-\gamma)]$ and the extrema are attained (Appendix A)
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - encoding: probability over the dataset drawn as in (2.4) → `dataProb`: the finite sum over datasets $D:\{1,\dots,N\}\to\mathcal S\times\mathcal A\times\mathcal B\times\mathcal S$ of $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$; reason: this is the law (2.4) on a finite sample space
--   - reading: no condition on $\gamma$ beyond $\gamma\in(0,1)$ in the item itself → $1/2\le\gamma<1$; reason: Appendix B proves Theorem 3, whose standing hypothesis is $1/2\le\gamma<1$ (p.13); the item is a step of that proof
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Lemma 3, p.16 (proof: Appendix C.4)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- Lemma 3 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.16): with probability exceeding `1 − δ`,
`Q⁻_pe ≤ Q^{µ̂,⋆}`, `Q⁺_pe ≥ Q^{⋆,ν̂}`, `V⁻_pe ≤ V^{µ̂,⋆}` and `V⁺_pe ≥ V^{⋆,ν̂}`, where `(µ̂, ν̂)`
is returned by Algorithm 1.

**Formalization Note.** The event holds for every output `(µ̂, ν̂)` of Algorithm 1 (every choice
of saddle points by `MatrixNash`). The algorithm's constant is quantified as `∃ C₀, ∀ C_b ≥ C₀`,
before the instance, and is run with the same `δ`. -/
theorem lemma_3 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cb : ℝ, C₀ ≤ Cb →
    ∀ (S A B : ℕ), 0 < S → 0 < A → 0 < B →
    ∀ (P : Kernel S A B) (r : Reward S A B), IsGame P r →
    ∀ γ : ℝ, 1 / 2 ≤ γ → γ < 1 →
    ∀ db : Fin S → Fin A → Fin B → ℝ, IsDist db →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ N : ℕ, 1 ≤ N →
      1 - δ < dataProb db P N (fun D =>
        ∀ (μh : Policy S A) (νh : Policy S B), IsVILCBOutput r γ Cb δ D μh νh →
          QpeMinus r γ Cb δ D ≤ QminBR P r γ μh ∧
          QmaxBR P r γ νh ≤ QpePlus r γ Cb δ D ∧
          VpeMinus r γ Cb δ D ≤ VminBR P r γ μh ∧
          VmaxBR P r γ νh ≤ VpePlus r γ Cb δ D) := by sorry

end OfflineZeroSumMG
