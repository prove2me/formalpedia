-- Prove2me | Theorems.Thm_KServer_workFnU_growth_2k_inj
-- name    : KServer.workFnU_growth_2k_inj
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:32:08.736598+00:00
-- url     : https://prove2.me/theorems/4d56dbf2-43b1-4226-b1ed-032b40224673
-- title:
--   Total growth of the unordered work function at injective configurations is at most $2k$ times the optimum
-- statement:
--   Fix an initial configuration $C_0$ and write $\widehat w_t$ for the unordered work function after the first $t$ requests of a sequence $\sigma$ of length $m$. Call a configuration **injective** when its $k$ servers occupy $k$ distinct points. Here $M$ is an arbitrary metric space and $k\ge1$ is arbitrary.
--
--   **Statement.** There is a constant $c$, depending on the metric space and on $C_0$ but not on the request sequence, such that for every $\sigma$ there are numbers $u_1,\dots,u_m$ with
--   $$\widehat w_t(X)\;\le\;\widehat w_{t-1}(X)+u_t\qquad\text{for every \emph{injective} configuration }X\text{ and every }t\le m,$$
--   $$\sum_{t=1}^{m}u_t\;\le\;2k\cdot\mathrm{OPT}(C_0,\sigma)+c .$$
--
--   **Role.** This is the central inequality of Koutsoupias and Papadimitriou's theorem that the Work Function Algorithm is $(2k-1)$-competitive --- still the best known upper bound for the $k$-server problem on a general metric space. It is proved from the *duality property* of work functions, which identifies the configurations maximising $\widehat w_t(X)-\widehat w_{t-1}(X)$ as the minimisers of $\widehat w_{t-1}(X)-d(r_t^{\,k},X)$, and that property is in turn a consequence of *quasiconvexity*. The potential used carries $2k$ work-function values, which is where the factor comes from; proving the $k$-server conjecture on general spaces amounts to replacing $2k$ by $k+1$ here.
--
--   By `KServer.extended_cost_lemma_injective`, a bound of this form with factor $\lambda$ makes the Work Function Algorithm $(\lambda-1)$-competitive; here $\lambda=2k$ gives the ratio $2k-1$. The statement mentions no online algorithm at all.
--
--   **Why the bound is asked only at injective configurations.** The classical theory takes a configuration to be a set of $k$ points, so the case of two servers sharing a point never arises; here a configuration is a labelled map and may be degenerate. The difference is real: at a single step the increment $\widehat w_t(X)-\widehat w_{t-1}(X)$ at a degenerate $X$ can exceed its value at every injective one --- this already happens on the uniform three-point space with $k=2$. So a bound proved by the classical argument is a bound at injective configurations, and `KServer.extended_cost_lemma_injective` is arranged to need no more: by `KServer.moveCost_injective_between` the Work Function Algorithm, started at an injective configuration, stays injective for ever.
--
--   **Formalization Note** The prefix $r_1,\dots,r_t$ appears as `σ.take t`, and the bounding sequence `u` is given explicitly rather than as a maximum over configurations, since on an unbounded metric space that maximum needs a separate finiteness argument. The proved case $\lambda=k+1$ on $k+1$ points, `KServer.workFnU_growth_card_succ_inj`, is the model for the shape of such an argument.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4, inequality (8) with the factor $2k$, and Theorem 3; originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128

import Mathlib
import Definitions.Def_KServer_workfunctionU

namespace KServer

theorem workFnU_growth_2k_inj (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (C₀ : Config k M) :
    ∃ c : ℝ, ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ (2 * (k : ℝ)) * offlineCost C₀ σ + c := by sorry

end KServer
