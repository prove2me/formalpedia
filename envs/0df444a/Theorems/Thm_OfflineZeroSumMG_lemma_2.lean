-- Prove2me | Theorems.Thm_OfflineZeroSumMG_lemma_2
-- name    : OfflineZeroSumMG.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:48.489729+00:00
-- url     : https://prove2.me/theorems/e063c6cc-d052-48cf-b9d3-93666b13745a
-- title:
--   Lemma 2 (corrected: $e\cdot\delta\le N$) — uniform Bernstein bounds near $V^{\mp\star}_{\mathsf{pe}}$
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   There are $C_0>0$ and a universal $\tilde c>0$, not depending on $C_{\mathsf b}$, such that the following holds for every $C_{\mathsf b}\ge C_0$. Let $1/2\le\gamma<1$, $\delta\in(0,1)$ and $e\cdot\delta\le N$, and let $V^{\mp\star}_{\mathsf{pe}}$ be the value functions of the fixed points of $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$. For any count vector $m$ with $\mathbb P\{N(\cdot)=m\}>0$, conditionally on $\{N(\cdot)=m\}$, with probability exceeding $1-\delta$, for all $(s,a,b)$ with $m(s,a,b)\ge1$,
--   $$\big|(\widehat P_{s,a,b}-P_{s,a,b})\widetilde V\big|\le\tilde c\sqrt{\frac{1}{N(s,a,b)}\mathrm{Var}_{\widehat P_{s,a,b}}(\widetilde V)\log\frac N\delta}+\tilde c\frac{\log\frac N\delta}{(1-\gamma)N(s,a,b)}\qquad\text{(B.9)}$$
--   and
--   $$\mathrm{Var}_{\widehat P_{s,a,b}}(\widetilde V)\le2\,\mathrm{Var}_{P_{s,a,b}}(\widetilde V)+\tilde c\frac{\log\frac N\delta}{(1-\gamma)^2N(s,a,b)}\qquad\text{(B.10)}$$
--   hold simultaneously for all $\widetilde V\in\mathbb R^S$ with $0\le\widetilde V\le\frac1{1-\gamma}$ and $\min\{\|\widetilde V-V^{-\star}_{\mathsf{pe}}\|_\infty,\|\widetilde V-V^{+\star}_{\mathsf{pe}}\|_\infty\}\le\frac1N$.
--
--   The point is that $\widetilde V$ may depend on the data through $V^{\mp\star}_{\mathsf{pe}}$; Lemma 2 is the decoupling step that justifies pessimism.
--
--   Differences from the source:
--   - reading: a "sufficiently large constant $C_{\mathsf b}>0$" in the algorithm and "some sufficiently large constant $\tilde c>0$" → $\exists C_0>0,\ \exists\tilde c>0,\ \forall C_{\mathsf b}\ge C_0$, quantified before every instance quantity; reason: $\tilde c$ comes from the universal constant of Claim 1 and does not involve $C_{\mathsf b}$ (p.27), and (B.11) takes $C_{\mathsf b}$ large relative to $\tilde c$, so $\tilde c$ cannot depend on $C_{\mathsf b}$; $\forall C_{\mathsf b}\ge C_0$ is the stronger reading of one fixed large $C_{\mathsf b}$ (R3)
--   - correction: no condition relating $N$ and $\delta$ → $e\cdot\delta\le N$, i.e. $\log(N/\delta)\ge1$; reason: the printed statement is false at $N=1$ with $\delta$ close to $1$ (paper.md C1: $S=2$, $A=B=1$, $\gamma=1/2$, $P(\cdot\mid s)$ uniform, $N=1$: every penalty is $\ge4$, so $V^{-\star}_{\mathsf{pe}}=0$, and $\widetilde V=1\{s\ne s'_1\}$ is within $1/N$ of it, with $|(\widehat P-P)\widetilde V|=1/2$ and $\mathrm{Var}_{\widehat P}(\widetilde V)=0$, while the right side of (B.9) is $2\tilde c\log(1/\delta)\to0$); the condition excludes only $N\in\{1,2\}$
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $\|\cdot\|_\infty$ → Mathlib's sup norm `‖·‖` on `Fin S → ℝ` and `Fin S → Fin A → Fin B → ℝ`; reason: on a finite product the sup norm is the $\ell_\infty$ norm
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - encoding: probability over the dataset drawn as in (2.4) → `dataProb`: the finite sum over datasets $D:\{1,\dots,N\}\to\mathcal S\times\mathcal A\times\mathcal B\times\mathcal S$ of $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$; reason: this is the law (2.4) on a finite sample space
--   - reading: no condition on $\gamma$ beyond $\gamma\in(0,1)$ in the item itself → $1/2\le\gamma<1$; reason: Appendix B proves Theorem 3, whose standing hypothesis is $1/2\le\gamma<1$ (p.13); the item is a step of that proof
--   - reading: "with probability exceeding $1-\delta$", proved conditionally on the counts (p.25) → for every count vector $m$ with positive probability, $\mathbb P(\{N(\cdot)=m\}\cap E)>(1-\delta)\mathbb P\{N(\cdot)=m\}$; reason: the proof's conditional statement (R4); it implies the unconditional one
--   - reading: "For any $(s,a,b)$ satisfying $N(s,a,b)\ge1$, with probability exceeding $1-\delta$" → one event $E$ that holds for all $(s,a,b)$ with $N(s,a,b)\ge1$; reason: the proof ends with this uniform statement (p.27) and the paper uses it so ((B.11), p.16; (C.47), p.36); it is the stronger reading, and a per-triple statement could not be union-bounded because $\delta$ is also a parameter of the algorithm
--   - encoding: $V^{\mp\star}_{\mathsf{pe}}$, the values of the unique fixed points → for every pair of fixed points `Qm`, `Qp` of the operators built from the same data; reason: the fixed points are unique (Lemma 1)
--   - reading: $O(\cdot)$ in (B.10) → the constant $\tilde c$; reason: a universal constant (R3)
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Lemma 2, (B.9)–(B.10), p.16 (proof: Appendix C.3, pp.23–29)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- Lemma 2 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.16), corrected (`e·δ ≤ N`): with
probability exceeding `1 − δ`, for all `(s, a, b)` with `N(s, a, b) ≥ 1`,

`|(P̂_{s,a,b} − P_{s,a,b})Ṽ| ≤ c̃ √((1/N(s,a,b)) Var_{P̂_{s,a,b}}(Ṽ) log(N/δ)) + c̃ log(N/δ)/((1−γ)N(s,a,b))` (B.9)

and `Var_{P̂_{s,a,b}}(Ṽ) ≤ 2 Var_{P_{s,a,b}}(Ṽ) + O(log(N/δ)/((1−γ)² N(s,a,b)))` (B.10) hold
simultaneously for all `Ṽ ∈ ℝ^S` with `0 ≤ Ṽ ≤ 1/(1−γ)` and
`min{‖Ṽ − V⁻⋆_pe‖_∞, ‖Ṽ − V⁺⋆_pe‖_∞} ≤ 1/N`.

**Formalization Note.** As in its proof (p.25), the probability is conditional on the count
vector: for every count vector `m` with positive probability, the conditional probability of the
event given `{N(·) = m}` exceeds `1 − δ`. The event is uniform over the triples with
`N(s, a, b) ≥ 1`: that is what the proof concludes (p.27) and how the paper uses the lemma
((B.11), p.16; (C.47), p.36). `V^∓⋆_pe` are the value functions of the fixed points of `T̂^∓_pe`
built from the same data (unique by Lemma 1), quantified as "every fixed point". The constant `c̃`
is universal and does not depend on `C_b` (p.27: it comes from the universal constant of Claim 1),
which (B.11) needs, since there `C_b` is large relative to `c̃`: `∃ C₀, ∃ c̃, ∀ C_b ≥ C₀`, before
the instance. `c̃` also serves as the constant of the `O(·)`. -/
theorem lemma_2 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ c : ℝ, 0 < c ∧ ∀ Cb : ℝ, C₀ ≤ Cb →
    ∀ (S A B : ℕ), 0 < S → 0 < A → 0 < B →
    ∀ (P : Kernel S A B) (r : Reward S A B), IsGame P r →
    ∀ γ : ℝ, 1 / 2 ≤ γ → γ < 1 →
    ∀ db : Fin S → Fin A → Fin B → ℝ, IsDist db →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ N : ℕ, Real.exp 1 * δ ≤ (N : ℝ) →
    ∀ m : Fin S → Fin A → Fin B → ℕ,
    0 < dataProb db P N (fun D => cnt D = m) →
      (1 - δ) * dataProb db P N (fun D => cnt D = m) <
      dataProb db P N (fun D => cnt D = m ∧
        ∀ (s : Fin S) (a : Fin A) (b : Fin B), 1 ≤ m s a b →
        ∀ Qm Qp : Fin S → Fin A → Fin B → ℝ,
          Tminus r γ Cb δ D Qm = Qm → Tplus r γ Cb δ D Qp = Qp →
        ∀ W : Fin S → ℝ, (∀ s', 0 ≤ W s' ∧ W s' ≤ 1 / (1 - γ)) →
          min ‖W - Vof Qm‖ ‖W - Vof Qp‖ ≤ 1 / (N : ℝ) →
          |∑ s', (Phat D s a b s' - P s a b s') * W s'| ≤
              c * Real.sqrt (1 / (cnt D s a b : ℝ) * varP (Phat D s a b) W *
                Real.log ((N : ℝ) / δ)) +
              c * Real.log ((N : ℝ) / δ) / ((1 - γ) * (cnt D s a b : ℝ)) ∧
          varP (Phat D s a b) W ≤
              2 * varP (P s a b) W +
              c * Real.log ((N : ℝ) / δ) / ((1 - γ) ^ 2 * (cnt D s a b : ℝ))) := by sorry

end OfflineZeroSumMG
