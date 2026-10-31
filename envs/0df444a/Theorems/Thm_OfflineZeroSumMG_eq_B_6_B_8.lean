-- Prove2me | Theorems.Thm_OfflineZeroSumMG_eq_B_6_B_8
-- name    : OfflineZeroSumMG.eq_B_6_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:40.381992+00:00
-- url     : https://prove2.me/theorems/14107052-de40-4dfa-82b6-0b02b69bdcdf
-- title:
--   (B.6)–(B.8) — the VI-LCB-Game iterates are within $1/N$ of the pessimistic fixed points
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   Assume $1/2\le\gamma<1$, $C_{\mathsf b}>0$, $\delta\in(0,1)$, $N\ge1$, and let $Q^{-\star}_{\mathsf{pe}}$, $Q^{+\star}_{\mathsf{pe}}$ be the fixed points of $\widehat{\mathcal T}^{-}_{\mathsf{pe}}$, $\widehat{\mathcal T}^{+}_{\mathsf{pe}}$ (Lemma 1) with value functions $V^{-\star}_{\mathsf{pe}}$, $V^{+\star}_{\mathsf{pe}}$ (3.3). For every dataset:
--
--   1. $Q^-_{\mathsf{pe},t}\le Q^{-\star}_{\mathsf{pe}}$ for all $t\ge0$, and hence $Q^-_{\mathsf{pe}}\le Q^{-\star}_{\mathsf{pe}}$ (B.6);
--   2. $\|V^-_{\mathsf{pe}}-V^{-\star}_{\mathsf{pe}}\|_\infty\le\|Q^-_{\mathsf{pe}}-Q^{-\star}_{\mathsf{pe}}\|_\infty\le\frac1N$ (B.7);
--   3. $Q^+_{\mathsf{pe}}\ge Q^{+\star}_{\mathsf{pe}}$, $\|Q^+_{\mathsf{pe}}-Q^{+\star}_{\mathsf{pe}}\|_\infty\le\frac1N$ and $\|V^+_{\mathsf{pe}}-V^{+\star}_{\mathsf{pe}}\|_\infty\le\frac1N$ (B.8).
--
--   The choice $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ is exactly what makes $\gamma^T/(1-\gamma)\le1/N$.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $\|\cdot\|_\infty$ → Mathlib's sup norm `‖·‖` on `Fin S → ℝ` and `Fin S → Fin A → Fin B → ℝ`; reason: on a finite product the sup norm is the $\ell_\infty$ norm
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - reading: no condition on $\gamma$ beyond $\gamma\in(0,1)$ in the item itself → $1/2\le\gamma<1$; reason: Appendix B proves Theorem 3, whose standing hypothesis is $1/2\le\gamma<1$ (p.13); the item is a step of that proof
--   - generalization: the algorithm's sufficiently large $C_{\mathsf b}$, its $\delta\in(0,1)$ and $N$ → every $C_{\mathsf b}>0$, every $\delta\in(0,1)$ and every dataset with $N\ge1$; reason: the item is deterministic and holds for all of them; it specializes to the paper's $C_{\mathsf b}$
--   - encoding: the unique fixed points $Q^{\mp\star}_{\mathsf{pe}}$ → arbitrary fixed points `Qm`, `Qp` given as hypotheses; reason: the fixed points are unique by Lemma 1, so these are the same objects
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), (B.6)–(B.8), p.15

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- (B.6)–(B.8) (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.15): with `Q⁻⋆_pe`, `Q⁺⋆_pe` the fixed
points of `T̂⁻_pe`, `T̂⁺_pe` and `V⁻⋆_pe`, `V⁺⋆_pe` their value functions (3.3),

* (B.6) `Q⁻_{pe,t} ≤ Q⁻⋆_pe` for all `t ≥ 0`, and hence `Q⁻_pe ≤ Q⁻⋆_pe`;
* (B.7) `‖V⁻_pe − V⁻⋆_pe‖_∞ ≤ ‖Q⁻_pe − Q⁻⋆_pe‖_∞ ≤ 1/N`;
* (B.8) `Q⁺_pe ≥ Q⁺⋆_pe`, `‖Q⁺_pe − Q⁺⋆_pe‖_∞ ≤ 1/N`, `‖V⁺_pe − V⁺⋆_pe‖_∞ ≤ 1/N`.

**Formalization Note.** `Qm`, `Qp` are arbitrary fixed points (unique by Lemma 1).
`Q^∓_pe = Q^∓_{pe,T}` with `T = ⌈log(N/(1−γ))/log(1/γ)⌉`. Stated for every dataset `D` with
`N ≥ 1`, `C_b > 0`, `δ ∈ (0,1)`, under the standing `1/2 ≤ γ < 1` of Theorem 3. -/
theorem eq_B_6_B_8 {S A B N : ℕ} (hS : 0 < S) (hA : 0 < A) (hB : 0 < B) (hN : 1 ≤ N)
    (r : Reward S A B) (hr : ∀ s a b, 0 ≤ r s a b ∧ r s a b ≤ 1)
    {γ Cb δ : ℝ} (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hCb : 0 < Cb) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (D : Fin N → Sample S A B) (Qm Qp : Fin S → Fin A → Fin B → ℝ)
    (hQm : Tminus r γ Cb δ D Qm = Qm) (hQp : Tplus r γ Cb δ D Qp = Qp) :
    (∀ t : ℕ, QminusIter r γ Cb δ D t ≤ Qm) ∧
    QpeMinus r γ Cb δ D ≤ Qm ∧
    ‖VpeMinus r γ Cb δ D - Vof Qm‖ ≤ ‖QpeMinus r γ Cb δ D - Qm‖ ∧
    ‖QpeMinus r γ Cb δ D - Qm‖ ≤ 1 / (N : ℝ) ∧
    Qp ≤ QpePlus r γ Cb δ D ∧
    ‖QpePlus r γ Cb δ D - Qp‖ ≤ 1 / (N : ℝ) ∧
    ‖VpePlus r γ Cb δ D - Vof Qp‖ ≤ 1 / (N : ℝ) := by sorry

end OfflineZeroSumMG
