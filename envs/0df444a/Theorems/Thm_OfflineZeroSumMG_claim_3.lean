-- Prove2me | Theorems.Thm_OfflineZeroSumMG_claim_3
-- name    : OfflineZeroSumMG.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:32.90766+00:00
-- url     : https://prove2.me/theorems/e225fbf3-624a-47d7-8866-f3800169258b
-- title:
--   Claim 3 — $\mathrm{Var}_{\widehat P_{s,a,b}}(V^-_{\mathsf{pe}})\le2\mathrm{Var}_{P_{s,a,b}}(V^-_{\mathsf{pe}})+c_4\frac{\log(N/\delta)}{(1-\gamma)^2Nd_{\mathsf b}(s,a,b)}$
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   There are $C_0>0$ and a universal constant $c_4>0$, not depending on $C_{\mathsf b}$, such that, for every $C_{\mathsf b}\ge C_0$, every game, $1/2\le\gamma<1$, $d_{\mathsf b}$, $\delta\in(0,1)$ and $N\ge1$, with probability exceeding $1-\delta$,
--   $$\mathrm{Var}_{\widehat P_{s,a,b}}(V^-_{\mathsf{pe}})\le2\,\mathrm{Var}_{P_{s,a,b}}(V^-_{\mathsf{pe}})+\frac{c_4\log\frac N\delta}{(1-\gamma)^2N\,d_{\mathsf b}(s,a,b)}$$
--   holds simultaneously for all $(s,a,b)$ with $d_{\mathsf b}(s,a,b)>0$.
--
--   It bounds the empirical variance inside the penalty by the true variance, which is then summed against the occupancy measure in Lemma 5.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - encoding: probability over the dataset drawn as in (2.4) → `dataProb`: the finite sum over datasets $D:\{1,\dots,N\}\to\mathcal S\times\mathcal A\times\mathcal B\times\mathcal S$ of $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$; reason: this is the law (2.4) on a finite sample space
--   - reading: no condition on $\gamma$ beyond $\gamma\in(0,1)$ in the item itself → $1/2\le\gamma<1$; reason: Appendix B proves Theorem 3, whose standing hypothesis is $1/2\le\gamma<1$ (p.13); the item is a step of that proof
--   - reading: "with probability exceeding $1-\delta$, there exists some universal constant $c_4>0$" and the algorithm's sufficiently large $C_{\mathsf b}$ → $\exists C_0>0,\ \exists c_4>0,\ \forall C_{\mathsf b}\ge C_0$, before the instance and outside the probability; reason: a universal constant does not depend on the data (R3); the proof (p.36) takes $c_4$ from the $O(\cdot)$ of Lemma 2 and from Claim 2, neither of which involves $C_{\mathsf b}$
--   - encoding: all $(s,a,b)$, where for $d_{\mathsf b}(s,a,b)=0$ the right side is $+\infty$ → all $(s,a,b)$ with $d_{\mathsf b}(s,a,b)>0$; reason: the excluded triples satisfy the printed inequality trivially; Lean's $x/0=0$ would change them
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Claim 3, p.32 (proof: Appendix C.6.2)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- Claim 3 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.32): with probability exceeding `1 − δ`,
`Var_{P̂_{s,a,b}}(V⁻_pe) ≤ 2 Var_{P_{s,a,b}}(V⁻_pe) + c₄ log(N/δ)/((1−γ)² N d_b(s, a, b))` holds
simultaneously for all `(s, a, b)`, for a universal constant `c₄ > 0`.

**Formalization Note.** `c₄` is universal, so it is quantified before `C_b`, the instance and the
probability: `∃ C₀, ∃ c₄, ∀ C_b ≥ C₀`. Its proof (p.36) takes it from the `O(·)` of Lemma 2 and
from Claim 2, neither of which involves `C_b`. Triples with `d_b(s, a, b) = 0`, where the
printed right-hand side is `+∞`, are excluded (Lean would read the fraction as `0`). -/
theorem claim_3 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ Cb : ℝ, C₀ ≤ Cb →
    ∀ (S A B : ℕ), 0 < S → 0 < A → 0 < B →
    ∀ (P : Kernel S A B) (r : Reward S A B), IsGame P r →
    ∀ γ : ℝ, 1 / 2 ≤ γ → γ < 1 →
    ∀ db : Fin S → Fin A → Fin B → ℝ, IsDist db →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ N : ℕ, 1 ≤ N →
      1 - δ < dataProb db P N (fun D => ∀ s a b, 0 < db s a b →
        varP (Phat D s a b) (VpeMinus r γ Cb δ D) ≤
          2 * varP (P s a b) (VpeMinus r γ Cb δ D) +
          c₄ * Real.log ((N : ℝ) / δ) / ((1 - γ) ^ 2 * (N : ℝ) * db s a b)) := by sorry

end OfflineZeroSumMG
