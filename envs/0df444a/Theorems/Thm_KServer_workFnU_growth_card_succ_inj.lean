-- Prove2me | Theorems.Thm_KServer_workFnU_growth_card_succ_inj
-- name    : KServer.workFnU_growth_card_succ_inj
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:21:16.623217+00:00
-- url     : https://prove2.me/theorems/4a821c04-76cd-4015-87dd-feebe89b8357
-- title:
--   Total growth of the unordered work function at injective configurations on $k+1$ points
-- statement:
--   Let $M$ be a metric space with exactly $k+1$ points, $k\ge1$, and fix an initial configuration $C_0$. Write $\widehat w_t$ for the unordered work function after the first $t$ requests of a sequence $\sigma$ of length $m$.
--
--   **Statement.** There is a constant $c$, depending on $M$ and $C_0$ but not on the request sequence, such that for every $\sigma$ there are numbers $u_1,\dots,u_m$ with
--   $$\widehat w_t(X)\;\le\;\widehat w_{t-1}(X)+u_t\quad\text{for every \emph{injective} configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;(k+1)\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--
--   **Role.** With `KServer.extended_cost_lemma_injective` this gives the Manasse--McGeoch--Sleator theorem that the $k$-server conjecture holds on every metric space of $k+1$ points: the Work Function Algorithm is $k$-competitive there.
--
--   **Why $k+1$.** On a space of $k+1$ points an injective configuration occupies all but one point, so it is determined, up to relabelling, by the single point it leaves uncovered — its *hole*. Since the unordered work function is unchanged by relabelling, it is a function of the hole alone, and there are exactly $k+1$ holes. The work function is nondecreasing in the request sequence, so each of the $k+1$ increments is nonnegative and the maximum over holes is at most their sum:
--   $$\max_{h}\bigl\{\widehat w_t(h)-\widehat w_{t-1}(h)\bigr\}\;\le\;\sum_{h}\bigl\{\widehat w_t(h)-\widehat w_{t-1}(h)\bigr\}.$$
--   Summing over $t$ telescopes each term separately, leaving $\sum_h\widehat w_m(h)-\sum_h\widehat w_0(h)$. Each $\widehat w_m(h)$ is within $k\cdot\mathrm{diam}(M)$ of the optimum, and each $\widehat w_0(h)$ is nonnegative, so the total is at most $(k+1)\bigl(\mathrm{OPT}+k\,\mathrm{diam}(M)\bigr)$. The factor $k+1$ is exactly the number of states of the induced one-token avoidance problem, and the additive constant is $(k+1)k\,\mathrm{diam}(M)$.
--
--   **Formalization Note** The bound is asserted only at injective configurations, which is what `KServer.extended_cost_lemma_injective` consumes. It is *not* the maximum over all maps `Fin k → M`: a configuration with two servers on one point can, at a single step, have a larger increment than any injective one, so the restriction is not cosmetic. `Fintype.card M = k + 1` makes $M$ itself the $(k+1)$-point space. The hole configurations are obtained from `Fintype.equivFinOfCardEq` applied to the subtype $\{x : x\ne p\}$, and the identification of an arbitrary injective $X$ with a relabelling of the hole configuration for the unique point missing from its image uses `Equiv.ofInjective` on both sides.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 2 (the $k+1$-point case) and Section 3.4 (the Extended Cost Lemma); originally M. Manasse, L. McGeoch, D. Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, https://doi.org/10.1016/0196-6774(90)90003-W

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_growth_card_succ_inj (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 1) (C₀ : Config k M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + c := by sorry

end KServer
