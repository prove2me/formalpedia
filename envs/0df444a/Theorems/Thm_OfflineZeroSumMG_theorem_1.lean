-- Prove2me | Theorems.Thm_OfflineZeroSumMG_theorem_1
-- name    : OfflineZeroSumMG.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:56.062438+00:00
-- url     : https://prove2.me/theorems/4610c494-2ed2-4b12-a3ed-39d73083a15f
-- title:
--   Theorem 1 (corrected: $e\cdot\delta\le N$) — VI-LCB-Game returns an $\varepsilon$-Nash pair from $\widetilde O\big(C^\star_{\mathsf{clipped}}S(A+B)/((1-\gamma)^3\varepsilon^2)\big)$ samples
-- statement:
--   Throughout, $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ is a discounted two-player zero-sum Markov game with $S$ states, $A$ max-player actions and $B$ min-player actions, transition kernel $P$ and rewards $r\in[0,1]$. The offline dataset consists of $N$ transitions $(s_i,a_i,b_i,s'_i)$ with $(s_i,a_i,b_i)$ i.i.d. $\sim d_{\mathsf b}$ and $s'_i\sim P(\cdot\mid s_i,a_i,b_i)$ (2.4); $N(s,a,b)$ are the counts, $\widehat P$ and $\widehat r$ the empirical model (3.1)–(3.2), $\beta(s,a,b;V)$ the penalty (3.5) with constant $C_{\mathsf b}$ and target $\delta$, $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$ the pessimistic operators (3.4), and $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$, $V^{\mp}_{\mathsf{pe}}$ the output of VI-LCB-Game (Algorithm 1) after $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$ rounds.
--
--   Let $\rho\in\Delta(\mathcal S)$ be any initial distribution, let $(\mu^\star,\nu^\star)$ be a Nash equilibrium with value $V^\star=V^{\mu^\star,\nu^\star}$, and suppose Assumption 2 holds with constant $C$ (for instance $C=C^\star_{\mathsf{clipped}}$). Assume $1/2\le\gamma<1$, $\delta\in(0,1)$ and $\varepsilon\in(0,\frac1{1-\gamma}]$. There is $C_0>0$ such that for every $C_{\mathsf b}\ge C_0$ there is a constant $c_1>0$ such that, whenever $e\cdot\delta\le N$ and
--   $$N\ge c_1\frac{CS(A+B)}{(1-\gamma)^3\varepsilon^2}\log\frac N\delta,$$
--   then with probability exceeding $1-\delta$, every policy pair $(\hat\mu,\hat\nu)$ returned by Algorithm 1 satisfies
--   $$V^\star(\rho)-\varepsilon\le V^{\hat\mu,\star}(\rho),\qquad V^{\star,\hat\nu}(\rho)\le V^\star(\rho)+\varepsilon,\qquad V^{\star,\hat\nu}(\rho)-V^{\hat\mu,\star}(\rho)\le\varepsilon.$$
--
--   The pair is thus an $\varepsilon$-approximate Nash equilibrium (duality gap at most $\varepsilon$), with a sample size linear in the number $A+B$ of individual actions rather than the number $AB$ of joint actions; Theorem 2 of the paper shows this is minimax-optimal up to log factors.
--
--   **Formalization Note** The printed conclusion $V^{\hat\mu,\star}(\rho)-\varepsilon\le V^\star(\rho)\le V^{\star,\hat\nu}(\rho)+\varepsilon$ holds for every policy pair by weak duality, so the intended $\varepsilon$-duality gap is stated. Nash equilibria exist (Shapley), saddle points of every matrix game exist (minimax theorem), and Assumption 2 holds whenever $d_{\mathsf b}>0$ everywhere, so no hypothesis is vacuous.
--
--   Differences from the source:
--   - reading: a "sufficiently large constant $C_{\mathsf b}>0$" in the algorithm and universal constants of the item → $\exists C_0>0,\ \forall C_{\mathsf b}\ge C_0,\ \exists$ (the item's constants) $>0$, quantified before every instance quantity; reason: the constants are universal (R3); $\forall C_{\mathsf b}\ge C_0$ is the stronger reading of one fixed large $C_{\mathsf b}$
--   - correction: no condition relating $N$ and $\delta$ → $e\cdot\delta\le N$, i.e. $\log(N/\delta)\ge1$; reason: the printed statement is false at $N=1$ with $\delta$ close to $1$ (paper.md C1: for the goal, $S=1$, $A=2$, $B=1$, rewards $1,0$, $\gamma=1/2$, $d_{\mathsf b}$ uniform, $\varepsilon=1/2$: every penalty is $\ge4$, so $Q^-_{\mathsf{pe}}\equiv0$ and MatrixNash may return the zero-reward action, while the sample-size condition $1\ge64c_1\log(1/\delta)$ holds for $\delta$ near $1$); the condition excludes only $N\in\{1,2\}$
--   - encoding: $C^\star_{\mathsf{clipped}}$ of (2.6) is finite, and the bound is stated with $C^\star_{\mathsf{clipped}}$ → any $C$ with $\min\{d,\,1/(S(A+B))\}\le C\,d_{\mathsf b}$ for all unilateral deviations (`IsClippedCoverage`), and the bound with $C$; reason: the predicate holds exactly when $C^\star_{\mathsf{clipped}}$ is finite and at most $C$, in particular for $C=C^\star_{\mathsf{clipped}}$, and the bound grows with $C$; the product form avoids Lean's $x/0=0$
--   - generalization: the policy pair returned by Algorithm 1, where MatrixNash returns "a solution" of the matrix game → every pair $(\hat\mu,\hat\nu)$ such that, at every state, $\hat\mu(s)$ is the max-player part of a saddle point of $Q^-_{\mathsf{pe}}(s,\cdot,\cdot)$ and $\hat\nu(s)$ the min-player part of a saddle point of $Q^+_{\mathsf{pe}}(s,\cdot,\cdot)$, inside one event; reason: implies the statement for every selection rule of MatrixNash; saddle points exist by the minimax theorem, so the set is nonempty
--   - encoding: $\mathcal S=\{1,\dots,S\}$, $\mathcal A=\{1,\dots,A\}$, $\mathcal B=\{1,\dots,B\}$ → `Fin S`, `Fin A`, `Fin B` (0-based) with $0<S$, $0<A$, $0<B$; reason: an index shift; same instances
--   - encoding: $V^{\mu,\nu}$, $Q^{\mu,\nu}$ as expected discounted sums; $V^{\mu,\star}=\min_\nu$, $V^{\star,\nu}=\max_\mu$; $V(\rho)=\mathbb E_{s\sim\rho}V(s)$ → $V^{\mu,\nu}(s)=\sum_t\gamma^t((P^{\mu,\nu})^t r^{\mu,\nu})(s)$, $Q^{\mu,\nu}$ by its first-step decomposition, best responses as real `⨅`/`⨆` over stationary randomized policies, $V(\rho)=\sum_s\rho(s)V(s)$; reason: the law of $s_t$ is the $t$-th matrix power; the families are nonempty and bounded in $[0,1/(1-\gamma)]$ and the extrema are attained (Appendix A)
--   - encoding: $d^{\mu,\nu}(s,a,b;\rho)$ of (2.2) → $d^{\mu,\nu}(s;\rho)\mu(a|s)\nu(b|s)$ with $d^{\mu,\nu}(s;\rho)=(1-\gamma)\sum_t\gamma^t(\rho^\top(P^{\mu,\nu})^t)(s)$; reason: this is (2.3), which the paper derives from (2.2)
--   - encoding: Algorithm 1 sets $V_{\mathsf{pe},t}(s)=\mathbb E_{a\sim\mu_t(s),b\sim\nu_t(s)}[Q_{\mathsf{pe},t}(s,a,b)]$ at the pair returned by MatrixNash → the operators and $V^{\mp}_{\mathsf{pe}}$ use the matrix-game value (3.3) of $Q_{\mathsf{pe},t}(s,\cdot,\cdot)$; reason: the expected payoff at every saddle point equals the value (proved in a verification file), so the iterates are the same
--   - encoding: (3.5) at $N(s,a,b)=0$, a division by zero → the branch $\beta=1/(1-\gamma)+4/N$; reason: the printed formula with $1/0=+\infty$ gives $\min\{+\infty,1/(1-\gamma)\}+4/N$; the paper uses this value on p.31
--   - encoding: probability over the dataset drawn as in (2.4) → `dataProb`: the finite sum over datasets $D:\{1,\dots,N\}\to\mathcal S\times\mathcal A\times\mathcal B\times\mathcal S$ of $\prod_i d_{\mathsf b}(s_i,a_i,b_i)P(s'_i\mid s_i,a_i,b_i)$; reason: this is the law (2.4) on a finite sample space
--   - reading: the printed conclusion $V^{\hat\mu,\star}(\rho)-\varepsilon\le V^\star(\rho)\le V^{\star,\hat\nu}(\rho)+\varepsilon$ → $V^\star(\rho)-\varepsilon\le V^{\hat\mu,\star}(\rho)$, $V^{\star,\hat\nu}(\rho)\le V^\star(\rho)+\varepsilon$ and $V^{\star,\hat\nu}(\rho)-V^{\hat\mu,\star}(\rho)\le\varepsilon$; reason: the printed form holds for every pair by weak duality (p.5; proved in a verification file); the paper's claim is the $\varepsilon$-duality gap (p.9, (3.11); p.14, "taking the right-hand side of (B.2) to be no larger than $\varepsilon$"; the abstract) (R1)
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), Theorem 1, p.8; derivation from Theorem 3, p.14

import Mathlib
import Definitions.Def_OfflineZeroSumMG_VILCBGame

namespace OfflineZeroSumMG

/-- Theorem 1 (Yan, Li, Chen & Fan, arXiv:2206.04044v2, p.8), read as the `ε`-duality gap and
corrected (`e·δ ≤ N`): for any initial distribution `ρ`, under Assumption 2, `1/2 ≤ γ < 1`,
`δ ∈ (0, 1)` and `ε ∈ (0, 1/(1−γ)]`, with probability exceeding `1 − δ` the pair `(µ̂, ν̂)` returned
by Algorithm 1 satisfies

`V⋆(ρ) − ε ≤ V^{µ̂,⋆}(ρ)`, `V^{⋆,ν̂}(ρ) ≤ V⋆(ρ) + ε` and `V^{⋆,ν̂}(ρ) − V^{µ̂,⋆}(ρ) ≤ ε`,

as long as `N ≥ c₁ C⋆_clipped S(A+B) log(N/δ)/((1−γ)³ε²)` for a sufficiently large constant
`c₁ > 0`.

**Formalization Note.**
1. The printed conclusion `V^{µ̂,⋆}(ρ) − ε ≤ V⋆(ρ) ≤ V^{⋆,ν̂}(ρ) + ε` holds for every policy pair
   by weak duality (p.5); the paper's intended claim is the `ε`-duality gap (p.9, (3.11); p.14,
   "by taking the right-hand side of (B.2) to be no larger than `ε`"), which is stated here.
2. `e·δ ≤ N` is added: without it the theorem fails at `N = 1` with `δ` close to `1`.
3. `V⋆ = V^{µ⋆,ν⋆}` for the Nash pair of Assumption 2; `C⋆_clipped` is replaced by any `C` with
   `IsClippedCoverage` (true for `C = C⋆_clipped`; larger `C` only strengthens the sample-size
   hypothesis).
4. The event holds for every output of Algorithm 1, i.e. every choice of saddle points by
   `MatrixNash`; saddle points exist by the minimax theorem, Nash equilibria of the discounted game
   exist (Shapley), and Assumption 2 holds e.g. whenever `d_b > 0` everywhere, so no hypothesis is
   vacuous.
5. Constants: `∃ C₀, ∀ C_b ≥ C₀, ∃ c₁`, before every instance quantity; the algorithm is run with
   the same `N` and `δ`. -/
theorem theorem_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cb : ℝ, C₀ ≤ Cb → ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (S A B : ℕ), 0 < S → 0 < A → 0 < B →
    ∀ (P : Kernel S A B) (r : Reward S A B), IsGame P r →
    ∀ γ : ℝ, 1 / 2 ≤ γ → γ < 1 →
    ∀ ρ : Fin S → ℝ, ρ ∈ stdSimplex ℝ (Fin S) →
    ∀ db : Fin S → Fin A → Fin B → ℝ, IsDist db →
    ∀ (μs : Policy S A) (νs : Policy S B), IsNash P r γ μs νs →
    ∀ C : ℝ, IsClippedCoverage P γ ρ db μs νs C →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (1 - γ) →
    ∀ N : ℕ, Real.exp 1 * δ ≤ (N : ℝ) →
      c₁ * (C * S * (A + B)) / ((1 - γ) ^ 3 * ε ^ 2) * Real.log ((N : ℝ) / δ) ≤ (N : ℝ) →
      1 - δ < dataProb db P N (fun D =>
        ∀ (μh : Policy S A) (νh : Policy S B), IsVILCBOutput r γ Cb δ D μh νh →
          atDist ρ (V P r γ μs νs) - ε ≤ atDist ρ (VminBR P r γ μh) ∧
          atDist ρ (VmaxBR P r γ νh) ≤ atDist ρ (V P r γ μs νs) + ε ∧
          atDist ρ (VmaxBR P r γ νh) - atDist ρ (VminBR P r γ μh) ≤ ε) := by sorry

end OfflineZeroSumMG
