-- Prove2me | Theorems.Thm_OfflineZeroSumMG_eq_B_4_B_5
-- name    : OfflineZeroSumMG.eq_B_4_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:45.387461+00:00
-- url     : https://prove2.me/theorems/5059e903-934d-4961-8a70-5dcea009e654
-- title:
--   (B.4)–(B.5) — the variance is $4/(1-\gamma)$-Lipschitz and the penalty $\beta$ is 2-Lipschitz on $[0,1/(1-\gamma)]^S$
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   1. For any probability row $p\in\Delta(\mathcal S)$ (such as $P_{s,a,b}$) and any $V_1,V_2:\mathcal S\to[0,\frac1{1-\gamma}]$,
--   $$\big|\mathrm{Var}_{p}(V_1)-\mathrm{Var}_{p}(V_2)\big|\le\frac4{1-\gamma}\|V_1-V_2\|_\infty.\qquad\text{(B.4)}$$
--   2. For any dataset, any $(s,a,b)$ and any $V_1,V_2:\mathcal S\to[0,\frac1{1-\gamma}]$, the penalties (3.5) obey
--   $$|\beta(s,a,b;V_1)-\beta(s,a,b;V_2)|\le2\|V_1-V_2\|_\infty.\qquad\text{(B.5)}$$
--
--   Here $\mathrm{Var}_p(V)=p(V\circ V)-(pV)^2$ (A.1). These Lipschitz bounds control how the penalty changes when $V$ moves within $1/N$, which the proofs of Lemma 1 and Lemma 4 use.
--
--   Differences from the source:
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $\|\cdot\|_\infty$ → Mathlib's sup norm `‖·‖` on `Fin S → ℝ` and `Fin S → Fin A → Fin B → ℝ`; reason: on a finite product the sup norm is the $\ell_\infty$ norm
--   - generalization: the standing $1/2\le\gamma<1$ of Theorem 3 (p.13) → $0<\gamma<1$, the range of the game (§2.1, p.4); reason: the item's own sentence has no condition on $\gamma$ and the statement holds on the whole range; it specializes to $\gamma\ge1/2$
--   - generalization: the algorithm's sufficiently large $C_{\mathsf b}$, its $\delta\in(0,1)$ and $N$ → every $C_{\mathsf b}>0$, every $\delta\in(0,1)$ and every dataset with $N\ge1$; reason: the item is deterministic and holds for all of them; it specializes to the paper's $C_{\mathsf b}$
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - encoding: "any probability transition kernel $P$ and any $(s,a,b)$" with the row $P_{s,a,b}$ → any probability vector $p\in\Delta(\mathcal S)$; reason: every probability vector is a row of some kernel, and every row is a probability vector
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), §B.1 items 2–3, (B.4)–(B.5), p.14

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- (B.4) and (B.5) (Yan, Li, Chen & Fan, arXiv:2206.04044v2, §B.1 items 2–3, p.14).

(B.4): for any `V₁, V₂ : S → [0, 1/(1−γ)]` and any probability row `p = P_{s,a,b}`,
`|Var_p(V₁) − Var_p(V₂)| ≤ (4/(1−γ)) ‖V₁ − V₂‖_∞`.

(B.5): for any `(s, a, b)` and any `V₁, V₂ : S → [0, 1/(1−γ)]`, the penalties (3.5) obey
`|β(s, a, b; V₁) − β(s, a, b; V₂)| ≤ 2 ‖V₁ − V₂‖_∞`.

**Formalization Note.** Stated for the whole range `0 < γ < 1` of the game (§2.1, p.4). (B.5) is
stated for every dataset `D` of `N ≥ 1` samples, every `C_b > 0` and
every `δ ∈ (0, 1)`. `‖·‖` is the sup norm. -/
theorem eq_B_4_B_5 {S A B : ℕ} (hS : 0 < S) (hA : 0 < A) (hB : 0 < B)
    {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    (∀ p : Fin S → ℝ, p ∈ stdSimplex ℝ (Fin S) →
      ∀ V₁ V₂ : Fin S → ℝ, (∀ s, 0 ≤ V₁ s ∧ V₁ s ≤ 1 / (1 - γ)) →
        (∀ s, 0 ≤ V₂ s ∧ V₂ s ≤ 1 / (1 - γ)) →
        |varP p V₁ - varP p V₂| ≤ 4 / (1 - γ) * ‖V₁ - V₂‖) ∧
    (∀ Cb δ : ℝ, 0 < Cb → 0 < δ → δ < 1 →
      ∀ N : ℕ, 1 ≤ N → ∀ (D : Fin N → Sample S A B) (s : Fin S) (a : Fin A) (b : Fin B),
      ∀ V₁ V₂ : Fin S → ℝ, (∀ s', 0 ≤ V₁ s' ∧ V₁ s' ≤ 1 / (1 - γ)) →
        (∀ s', 0 ≤ V₂ s' ∧ V₂ s' ≤ 1 / (1 - γ)) →
        |beta γ Cb δ D s a b V₁ - beta γ Cb δ D s a b V₂| ≤ 2 * ‖V₁ - V₂‖) := by sorry

end OfflineZeroSumMG
