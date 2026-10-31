-- Prove2me | Theorems.Thm_OfflineZeroSumMG_eq_B_11
-- name    : OfflineZeroSumMG.eq_B_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:54.842806+00:00
-- url     : https://prove2.me/theorems/d564a0c0-779c-4286-b516-4333fad97cc3
-- title:
--   (B.11) — on the event of (B.9) the penalty dominates the deviation: $|(\widehat P-P)\widetilde V|+4/N\le\beta(\widetilde V)$
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   For every $\tilde c>0$ there is $C_0>0$ (depending only on $\tilde c$) such that for every $C_{\mathsf b}\ge C_0$, every $0<\gamma<1$, $\delta\in(0,1)$, every dataset, every $(s,a,b)$ with $N(s,a,b)\ge1$ and every $\widetilde V:\mathcal S\to[0,\frac1{1-\gamma}]$: if $\widetilde V$ satisfies (B.9) with the constant $\tilde c$, then
--   $$\big|(\widehat P_{s,a,b}-P_{s,a,b})\widetilde V\big|+\frac4N\le\beta(s,a,b;\widetilde V).$$
--
--   On the event of Lemma 2 this holds for every $\widetilde V$ satisfying the conditions of Lemma 2, which is how the paper uses it: the penalty is a valid confidence width, so the pessimistic estimates stay below the true values.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - generalization: the standing $1/2\le\gamma<1$ of Theorem 3 (p.13) → $0<\gamma<1$, the range of the game (§2.1, p.4); reason: the item's own sentence has no condition on $\gamma$ and the statement holds on the whole range; it specializes to $\gamma\ge1/2$
--   - reading: "holds for any $(s,a,b)$ … and any $\widetilde V$ satisfying the conditions in Lemma 2", with $\tilde c$ of Lemma 2 and the algorithm's sufficiently large $C_{\mathsf b}$ → $\forall\tilde c>0,\ \exists C_0>0,\ \forall C_{\mathsf b}\ge C_0$, before the instance; reason: $C_{\mathsf b}$ must be large relative to $\tilde c$; $\forall C_{\mathsf b}\ge C_0$ is the stronger reading
--   - generalization: $\widetilde V$ in Lemma 2's set, on Lemma 2's event → every $\widetilde V\in[0,1/(1-\gamma)]^S$ that satisfies (B.9), for every dataset; reason: on Lemma 2's event every $\widetilde V$ of Lemma 2's set satisfies (B.9), so this implies the paper's claim
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), (B.11), p.16

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- (B.11) (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.16): the penalty dominates the deviation,
`|(P̂_{s,a,b} − P_{s,a,b})Ṽ| + 4/N ≤ β(s, a, b; Ṽ)` for any `(s, a, b)` with `N(s, a, b) ≥ 1` and any
`Ṽ` satisfying the conditions of Lemma 2.

**Formalization Note.** This is the deterministic step from (B.9) to (B.11): for every constant
`c̃ > 0` there is `C₀` such that for every `C_b ≥ C₀`, every dataset, every `(s, a, b)` with
`N(s, a, b) ≥ 1` and every `Ṽ ∈ [0, 1/(1−γ)]^S` satisfying (B.9) with `c̃`, (B.11) holds. It
therefore applies on the event of Lemma 2 and to any other `Ṽ` satisfying (B.9). -/
theorem eq_B_11 :
    ∀ c : ℝ, 0 < c → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cb : ℝ, C₀ ≤ Cb →
    ∀ (S A B N : ℕ), 0 < S → 0 < A → 0 < B →
    ∀ P : Kernel S A B, (∀ s a b, P s a b ∈ stdSimplex ℝ (Fin S)) →
    ∀ γ : ℝ, 0 < γ → γ < 1 →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (D : Fin N → Sample S A B) (s : Fin S) (a : Fin A) (b : Fin B), 1 ≤ cnt D s a b →
    ∀ W : Fin S → ℝ, (∀ s', 0 ≤ W s' ∧ W s' ≤ 1 / (1 - γ)) →
      |∑ s', (Phat D s a b s' - P s a b s') * W s'| ≤
          c * Real.sqrt (1 / (cnt D s a b : ℝ) * varP (Phat D s a b) W *
            Real.log ((N : ℝ) / δ)) +
          c * Real.log ((N : ℝ) / δ) / ((1 - γ) * (cnt D s a b : ℝ)) →
      |∑ s', (Phat D s a b s' - P s a b s') * W s'| + 4 / (N : ℝ) ≤
          beta γ Cb δ D s a b W := by sorry

end OfflineZeroSumMG
