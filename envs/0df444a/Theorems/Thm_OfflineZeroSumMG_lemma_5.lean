-- Prove2me | Theorems.Thm_OfflineZeroSumMG_lemma_5
-- name    : OfflineZeroSumMG.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:38.665632+00:00
-- url     : https://prove2.me/theorems/30923ac4-5dff-49b8-a8b8-77bf4b8a5751
-- title:
--   Lemma 5 (corrected: $e\cdot\delta\le N$) — occupancy-weighted penalty bound
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   Let $\rho\in\Delta(\mathcal S)$, let $(\mu^\star,\nu^\star)$ be a Nash equilibrium and let $C$ satisfy Assumption 2 for it (for instance $C=C^\star_{\mathsf{clipped}}$). For a deterministic $f$ with $f(s)\in\arg\min_b\sum_a\mu^\star(a\mid s)Q^-_{\mathsf{pe}}(s,a,b)$ let $\nu_0=1_f$ and $\beta^{\mu^\star,\nu_0}$ as in (B.15b). There is $C_0>0$ such that for every $C_{\mathsf b}\ge C_0$ there is a universal $c_6>0$ such that, for every game, $1/2\le\gamma<1$, $\rho$, $d_{\mathsf b}$, Nash pair, $C$, $\delta\in(0,1)$ and $N$ with $e\cdot\delta\le N$: with probability exceeding $1-\delta$, for every such $f$,
--   $$(d^{\mu^\star,\nu_0})^\top\beta^{\mu^\star,\nu_0}\le c_6\frac{CS(A+B)}{(1-\gamma)N}\log\frac N\delta+c_6\sqrt{\frac{CS(A+B)}{N(1-\gamma)}\log\frac N\delta}.$$
--
--   Combined with (B.21) this yields the bound (B.1a) of Theorem 3.
--
--   Differences from the source:
--   - reading: a "sufficiently large constant $C_{\mathsf b}>0$" in the algorithm and universal constants of the item → $\exists C_0>0,\ \forall C_{\mathsf b}\ge C_0,\ \exists$ (the item's constants) $>0$, quantified before every instance quantity; reason: the constants are universal (R3); $\forall C_{\mathsf b}\ge C_0$ is the stronger reading of one fixed large $C_{\mathsf b}$
--   - correction: no condition relating $N$ and $\delta$ → $e\cdot\delta\le N$, i.e. $\log(N/\delta)\ge1$; reason: the printed statement is false at $N=1$ with $\delta$ close to $1$ (paper.md C1: $S=A=B=1$, $\gamma=1/2$, $N=1$, where $C^\star_{\mathsf{clipped}}=1/2$: the left side is $\ge4/N=4$ for every dataset (proved in a verification file), while the right side $2c_6\log(1/\delta)+c_6\sqrt{2\log(1/\delta)}\to0$); the condition excludes only $N\in\{1,2\}$
--   - encoding: $C^\star_{\mathsf{clipped}}$ of (2.6) is finite, and the bound is stated with $C^\star_{\mathsf{clipped}}$ → any $C$ with $\min\{d,\,1/(S(A+B))\}\le C\,d_{\mathsf b}$ for all unilateral deviations (`IsClippedCoverage`), and the bound with $C$; reason: the predicate holds exactly when $C^\star_{\mathsf{clipped}}$ is finite and at most $C$, in particular for $C=C^\star_{\mathsf{clipped}}$, and the bound grows with $C$; the product form avoids Lean's $x/0=0$
--   - reading: $\nu_0$ of (B.13), and (B.14)'s "for instance" $b_s=\arg\max_b\langle\mu^\star(s),Q^-_{\mathsf{pe}}(s,\cdot,b)\rangle$ → $\nu_0=1_{f(s)}$ with $f(s)\in\arg\min_b\sum_a\mu^\star(a|s)Q^-_{\mathsf{pe}}(s,a,b)$; reason: (B.13) defines $\nu_0(s)$ as a minimizer; the arg max of (B.14) is not one (a typo, R2), and the proof (C.39) uses the minimizer
--   - generalization: one deterministic minimizer $\nu_0$ chosen by the proof → every deterministic minimizer $f$, inside the event; reason: implies the statement for the chosen $\nu_0$
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $V^{\mu,\nu}$, $Q^{\mu,\nu}$ as expected discounted sums; $V^{\mu,\star}=\min_\nu$, $V^{\star,\nu}=\max_\mu$; $V(\rho)=\mathbb E_{s\sim\rho}V(s)$ → $V^{\mu,\nu}(s)=\sum_t\gamma^t((P^{\mu,\nu})^t r^{\mu,\nu})(s)$, $Q^{\mu,\nu}$ by its first-step decomposition, best responses as real `⨅`/`⨆` over stationary randomized policies, $V(\rho)=\sum_s\rho(s)V(s)$; reason: the law of $s_t$ is the $t$-th matrix power; the families are nonempty and bounded in $[0,1/(1-\gamma)]$ and the extrema are attained (Appendix A)
--   - encoding: $d^{\mu,\nu}(s,a,b;\rho)$ of (2.2) → $d^{\mu,\nu}(s;\rho)\mu(a|s)\nu(b|s)$ with $d^{\mu,\nu}(s;\rho)=(1-\gamma)\sum_t\gamma^t(\rho^\top(P^{\mu,\nu})^t)(s)$; reason: this is (2.3), which the paper derives from (2.2)
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - encoding: probability over the dataset drawn as in (2.4) → `dataProb`: the finite sum over datasets $D:\{1,\dots,N\}\to\mathcal S\times\mathcal A\times\mathcal B\times\mathcal S$ of $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$; reason: this is the law (2.4) on a finite sample space
--   - reading: no condition on $\gamma$ beyond $\gamma\in(0,1)$ in the item itself → $1/2\le\gamma<1$; reason: Appendix B proves Theorem 3, whose standing hypothesis is $1/2\le\gamma<1$ (p.13); the item is a step of that proof
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Lemma 5, p.17 (proof: Appendix C.6, pp.31–36)

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- Lemma 5 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.17), corrected (`e·δ ≤ N`): there is a
universal `c₆ > 0` such that, with probability exceeding `1 − δ`,

`(d^{µ⋆,ν₀})⊤ β^{µ⋆,ν₀} ≤ c₆ (C⋆_clipped S(A+B)/((1−γ)N)) log(N/δ)
  + c₆ √((C⋆_clipped S(A+B)/(N(1−γ))) log(N/δ))`,

with `ν₀` as in (B.13) and `β^{µ⋆,ν₀}` from (B.15b) at `V = V⁻_pe`.

**Formalization Note.** `C⋆_clipped` is replaced by any `C` satisfying Assumption 2 for the Nash
pair `(µ⋆, ν⋆)` (`IsClippedCoverage`, true for `C = C⋆_clipped`); the bound is monotone in `C`.
The event holds for every deterministic minimizer `ν₀ = purePolicy f` of (B.13). Constants:
`∃ C₀, ∀ C_b ≥ C₀, ∃ c₆`, before the instance. -/
theorem lemma_5 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cb : ℝ, C₀ ≤ Cb → ∃ c₆ : ℝ, 0 < c₆ ∧
    ∀ (S A B : ℕ), 0 < S → 0 < A → 0 < B →
    ∀ (P : Kernel S A B) (r : Reward S A B), IsGame P r →
    ∀ γ : ℝ, 1 / 2 ≤ γ → γ < 1 →
    ∀ ρ : Fin S → ℝ, ρ ∈ stdSimplex ℝ (Fin S) →
    ∀ db : Fin S → Fin A → Fin B → ℝ, IsDist db →
    ∀ (μs : Policy S A) (νs : Policy S B), IsNash P r γ μs νs →
    ∀ C : ℝ, IsClippedCoverage P γ ρ db μs νs C →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ N : ℕ, Real.exp 1 * δ ≤ (N : ℝ) →
      1 - δ < dataProb db P N (fun D =>
        ∀ f : Fin S → Fin B,
          (∀ s (b' : Fin B), ∑ a, (μs s : Fin A → ℝ) a * QpeMinus r γ Cb δ D s a (f s) ≤
                              ∑ a, (μs s : Fin A → ℝ) a * QpeMinus r γ Cb δ D s a b') →
          ∑ s, occState P γ ρ μs (purePolicy f) s *
              betaPol γ Cb δ D μs (purePolicy f) (VpeMinus r γ Cb δ D) s ≤
            c₆ * (C * S * (A + B) / ((1 - γ) * N)) * Real.log ((N : ℝ) / δ) +
            c₆ * Real.sqrt (C * S * (A + B) / ((N : ℝ) * (1 - γ)) *
              Real.log ((N : ℝ) / δ))) := by sorry

end OfflineZeroSumMG
