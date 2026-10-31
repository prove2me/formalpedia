-- Prove2me | Theorems.Thm_OfflineZeroSumMG_lemma_1
-- name    : OfflineZeroSumMG.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:54.328365+00:00
-- url     : https://prove2.me/theorems/e14021d6-86c7-4db8-9231-b7e98a466aab
-- title:
--   Lemma 1 (corrected: on the box $[0,1/(1-\gamma)]$) — monotonicity, $\gamma$-contraction and fixed points of $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   Assume $1/2\le\gamma<1$, $C_{\mathsf b}>0$, $\delta\in(0,1)$ and $N\ge1$, and call $\mathcal Q=[0,\frac1{1-\gamma}]^{\mathcal S\times\mathcal A\times\mathcal B}$ the box. For every dataset:
--
--   1. **(Monotonicity)** for $Q_1,Q_2\in\mathcal Q$ with $Q_1\ge Q_2$, $\widehat{\mathcal T}^-_{\mathsf{pe}}(Q_1)\ge\widehat{\mathcal T}^-_{\mathsf{pe}}(Q_2)$ and $\widehat{\mathcal T}^+_{\mathsf{pe}}(Q_1)\ge\widehat{\mathcal T}^+_{\mathsf{pe}}(Q_2)$;
--   2. **(Contraction)** for $Q_1,Q_2\in\mathcal Q$,
--   $$\|\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}(Q_1)-\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}(Q_2)\|_\infty\le\gamma\|Q_1-Q_2\|_\infty;$$
--   3. **(Fixed points)** $\widehat{\mathcal T}^-_{\mathsf{pe}}$ has a unique fixed point $Q^{-\star}_{\mathsf{pe}}$, $\widehat{\mathcal T}^+_{\mathsf{pe}}$ has a unique fixed point $Q^{+\star}_{\mathsf{pe}}$, and every fixed point satisfies $0\le Q^{\mp\star}_{\mathsf{pe}}(s,a,b)\le\frac1{1-\gamma}$.
--
--   These properties make the pessimistic value iterations converge geometrically to $Q^{\mp\star}_{\mathsf{pe}}$, so the analysis can work with the fixed points.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $\|\cdot\|_\infty$ → Mathlib's sup norm `‖·‖` on `Fin S → ℝ` and `Fin S → Fin A → Fin B → ℝ`; reason: on a finite product the sup norm is the $\ell_\infty$ norm
--   - encoding: $\max_{\mu_s\in\Delta(\mathcal A)}\min_{\nu_s\in\Delta(\mathcal B)}$ in (3.3) → real `⨆`/`⨅` over `stdSimplex` (`gval`, via the published `TheoryOfGames.Minimax.minK`); reason: the simplices are nonempty and compact and the payoff is continuous, so the sup and inf are the attained max and min
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - reading: no condition on $\gamma$ beyond $\gamma\in(0,1)$ in the item itself → $1/2\le\gamma<1$; reason: Appendix B proves Theorem 3, whose standing hypothesis is $1/2\le\gamma<1$ (p.13); the item is a step of that proof
--   - generalization: the algorithm's sufficiently large $C_{\mathsf b}$, its $\delta\in(0,1)$ and $N$ → every $C_{\mathsf b}>0$, every $\delta\in(0,1)$ and every dataset with $N\ge1$; reason: the item is deterministic and holds for all of them; it specializes to the paper's $C_{\mathsf b}$
--   - correction: bullets 1–2 "for any $Q_1\ge Q_2$" and "for any $Q_1$ and $Q_2$" → for $Q_1,Q_2$ in the box $[0,1/(1-\gamma)]^{\mathcal S\times\mathcal A\times\mathcal B}$; reason: false outside the box (paper.md C2: $S=2$, $A=B=1$, $\gamma=1/2$, $\widehat r=1$, $\widehat P=(0.1,0.9)$, $C_{\mathsf b}\log(N/\delta)/N(s,a,b)=0.1$, $V_2=(5,0)\le V_1=(5.5,0)$ give $\widehat{\mathcal T}^-_{\mathsf{pe}}$ values $0.776>0.753$ up to the common $-4/N$, and the gradient has $\ell_1$ norm $0.59>\gamma$); the proof (Appendix C.2) works in the box, and bullet 3 is unchanged
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Lemma 1, p.15 (proof: Appendix C.2, pp.20–23)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- Lemma 1 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.15), corrected: monotonicity and
`γ`-contraction of `T̂⁻_pe` and `T̂⁺_pe` on the box `[0, 1/(1−γ)]^{S×A×B}`, and uniqueness of their
fixed points, which lie in the box.

1. (Monotonicity) for `Q₁ ≥ Q₂` in the box, `T̂⁻_pe(Q₁) ≥ T̂⁻_pe(Q₂)` and `T̂⁺_pe(Q₁) ≥ T̂⁺_pe(Q₂)`;
2. (Contraction) for `Q₁, Q₂` in the box, `‖T̂^∓_pe(Q₁) − T̂^∓_pe(Q₂)‖_∞ ≤ γ ‖Q₁ − Q₂‖_∞`;
3. (Fixed points) `T̂⁻_pe` (resp. `T̂⁺_pe`) has a unique fixed point, and every fixed point lies in
   the box.

**Formalization Note.** The printed bullets 1–2 quantify over all `Q₁ ≥ Q₂` and all `Q₁, Q₂`;
outside the box both fail (counterexample in the item's natural-language statement), and the
proof (Appendix C.2) works inside the box with `γ ≥ 1/2`, the standing hypothesis of Theorem 3.
Stated for every dataset `D` with `N ≥ 1`, every `C_b > 0`, `δ ∈ (0, 1)`. `≤` on functions is
pointwise. -/
theorem lemma_1 {S A B N : ℕ} (hS : 0 < S) (hA : 0 < A) (hB : 0 < B) (hN : 1 ≤ N)
    (r : Reward S A B) (hr : ∀ s a b, 0 ≤ r s a b ∧ r s a b ≤ 1)
    {γ Cb δ : ℝ} (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hCb : 0 < Cb) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (D : Fin N → Sample S A B) :
    (∀ Q₁ Q₂ : Fin S → Fin A → Fin B → ℝ,
      (∀ s a b, 0 ≤ Q₁ s a b ∧ Q₁ s a b ≤ 1 / (1 - γ)) →
      (∀ s a b, 0 ≤ Q₂ s a b ∧ Q₂ s a b ≤ 1 / (1 - γ)) → Q₂ ≤ Q₁ →
        Tminus r γ Cb δ D Q₂ ≤ Tminus r γ Cb δ D Q₁ ∧
        Tplus r γ Cb δ D Q₂ ≤ Tplus r γ Cb δ D Q₁) ∧
    (∀ Q₁ Q₂ : Fin S → Fin A → Fin B → ℝ,
      (∀ s a b, 0 ≤ Q₁ s a b ∧ Q₁ s a b ≤ 1 / (1 - γ)) →
      (∀ s a b, 0 ≤ Q₂ s a b ∧ Q₂ s a b ≤ 1 / (1 - γ)) →
        ‖Tminus r γ Cb δ D Q₁ - Tminus r γ Cb δ D Q₂‖ ≤ γ * ‖Q₁ - Q₂‖ ∧
        ‖Tplus r γ Cb δ D Q₁ - Tplus r γ Cb δ D Q₂‖ ≤ γ * ‖Q₁ - Q₂‖) ∧
    (∃! Q : Fin S → Fin A → Fin B → ℝ, Tminus r γ Cb δ D Q = Q) ∧
    (∀ Q : Fin S → Fin A → Fin B → ℝ, Tminus r γ Cb δ D Q = Q →
      ∀ s a b, 0 ≤ Q s a b ∧ Q s a b ≤ 1 / (1 - γ)) ∧
    (∃! Q : Fin S → Fin A → Fin B → ℝ, Tplus r γ Cb δ D Q = Q) ∧
    (∀ Q : Fin S → Fin A → Fin B → ℝ, Tplus r γ Cb δ D Q = Q →
      ∀ s a b, 0 ≤ Q s a b ∧ Q s a b ≤ 1 / (1 - γ)) := by sorry

end OfflineZeroSumMG
