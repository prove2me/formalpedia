-- Prove2me | Theorems.Thm_NestedCRP_gibbs_posterior_stationary
-- name    : NestedCRP.gibbs_posterior_stationary
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:07.589501+00:00
-- url     : https://prove2.me/theorems/32321b3d-566c-4041-abfd-0549b5f537d5
-- title:
--   The hLDA collapsed Gibbs chain has the posterior as its unique stationary law and converges to it
-- statement:
--   Let $\gamma,\eta,\pi>0$ and $m\in(0,1)$, let $V\ge1$, and let $w$ be any corpus of $D$ documents. Let $P$ be one sweep of the collapsed Gibbs sampler for hLDA, built from Eqs. (2) and (4) on the countable state space of (tree, level allocations), with unbounded depth and branching, and let $\Pi$ be the posterior $p(c_{1:D},z_{1:D}\mid\gamma,\eta,m,\pi,w_{1:D})$. Then:
--
--   1. $\Pi$ is stationary for $P$;
--   2. $\Pi$ is the only stationary probability law of $P$;
--   3. from every state $x$, the $t$-step laws converge to $\Pi$ in total variation:
--
--   $$
--   \bigl\|P^t(x,\cdot)-\Pi\bigr\|_{TV}\xrightarrow[t\to\infty]{}0.
--   $$
--
--   The paper has no labelled theorem. This is its one mathematical claim about the sampler: "The stationary distribution of the corresponding Markov chain is the conditional distribution of the latent variables in the hLDA model given the corpus", and "this algorithm is guaranteed to converge in the limit". It is what justifies collecting samples after burn-in.
--
--   **Formalization Note** The sweep draws Eqs. (2) and (4) exactly, and the posterior is defined by the genuine Beta and Dirichlet integrals, so none of the conditionals is assumed.
--
--   Differences from the source:
--   - reading: "The stationary distribution" → stationary and the only stationary law; reason: "the" asserts uniqueness; this is the stronger reading
--   - reading: "guaranteed to converge in the limit" → total-variation convergence from every state; reason: the stronger reading of the sentence
--   - reading: step (b) draws from Eq. (2), for which §5.1 offers a staged Bernoulli recipe → an exact draw from Eq. (2) with the normalized word predictive; reason: the printed Bernoulli step is false (one document, one word, V = 2, m = ½, η = ½: it gives P(z = 1) = ¼, the truth is ½), and the numerator of Eq. (3) alone gives a different chain
--   - encoding: paths through an infinite tree of labelled restaurants, 1-based levels → a countable state space of nested partitions separated at a finite level, 0-based levels; reason: labels would leak information under conditioning, and the separation holds almost surely
--   - encoding: a vocabulary of V words, nonempty implicitly → [NeZero V], that is V ≥ 1; reason: nondegeneracy only: at V = 0 the symmetric Dirichlet on the empty simplex is undefined and the Γ(Vη) = Γ(0) factors of the path weights are poles; no instance of the source is excluded
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.3, p.7:17

import Mathlib
import Definitions.Def_mm_countable
import Definitions.Def_NestedCRP_posterior
import Definitions.Def_NestedCRP_sweep
open MarkovMixing

namespace NestedCRP

/-- "The stationary distribution of the corresponding Markov chain is the conditional distribution
of the latent variables in the hLDA model given the corpus", and "this algorithm is guaranteed to
converge in the limit": for all hyperparameters and every corpus, the posterior is stationary for
the sweep, it is the only stationary law, and the `t`-step laws converge to it in total variation
from every state. Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.3, p.7:17.

**Formalization Note** The tree has unbounded depth and branching and levels are all of `ℕ`. The
sweep draws Eqs. (2) and (4) exactly; the staged Bernoulli recipe of §5.1 is not used. -/
theorem gibbs_posterior_stationary {V D : ℕ} [NeZero V] (H : Hyper) (C : Corpus V D) :
    IsStationaryC (sweep H C) (posterior H C) ∧
      (∀ p : C.State → ℝ, IsStationaryC (sweep H C) p → p = posterior H C) ∧
      ∀ x : C.State, Filter.Tendsto
        (fun t => tvDistC (fun y => stepPow (sweep H C) t x y) (posterior H C))
        Filter.atTop (nhds 0) := by sorry

end NestedCRP
