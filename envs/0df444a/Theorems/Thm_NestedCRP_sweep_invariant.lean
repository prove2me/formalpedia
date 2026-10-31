-- Prove2me | Theorems.Thm_NestedCRP_sweep_invariant
-- name    : NestedCRP.sweep_invariant
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:02.48953+00:00
-- url     : https://prove2.me/theorems/3a7452aa-eea0-49a7-867a-de42c92d8768
-- title:
--   Each Gibbs update, and the sweep, leaves the posterior invariant
-- statement:
--   Each path kernel and each level kernel is a stochastic kernel on the state space with the posterior $\Pi$ as a stationary law, and so is the sweep:
--
--   $$
--   \sum_x\Pi(x)\,P(x,y)=\Pi(y)\qquad\text{for all states }y.
--   $$
--
--   This is the stationarity clause of the goal, and it rests on the closed forms of Eqs. (2) and (4) being the true conditionals.
--
--   Differences from the source:
--   - reading: step (b): "Randomly draw z from Eq. (2)", with §5.1 offering a staged Bernoulli recipe for it → an exact draw from Eq. (2) over all levels; reason: the printed Bernoulli step is false (one document, one word, V = 2, m = ½, η = ½: it gives P(z = 1) = ¼, the truth is ½); §5.3 says to draw from Eq. (2)
--   - reading: "sample each variable conditioned on the rest", no claim stated for a single step → each kernel is stochastic and stationary as well as the sweep; reason: this is what the sentence of §5.3 means for a Gibbs sampler
--   - encoding: a vocabulary of V words, nonempty implicitly → [NeZero V], that is V ≥ 1; reason: nondegeneracy only: at V = 0 the symmetric Dirichlet on the empty simplex is undefined and the Γ(Vη) = Γ(0) factors of the path weights are poles; no instance of the source is excluded
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §5.3, p.7:17

import Mathlib
import Definitions.Def_mm_countable
import Definitions.Def_NestedCRP_posterior
import Definitions.Def_NestedCRP_sweep
open MarkovMixing

namespace NestedCRP

/-- Each site update is a stochastic kernel leaving the posterior invariant, and so is the sweep.
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §5.3, p.7:17. -/
theorem sweep_invariant {V D : ℕ} [NeZero V] (H : Hyper) (C : Corpus V D) :
    (∀ d, IsStochasticC (pathKernel H C d) ∧ IsStationaryC (pathKernel H C d) (posterior H C)) ∧
      (∀ s, IsStochasticC (levelKernel H C s) ∧
        IsStationaryC (levelKernel H C s) (posterior H C)) ∧
      IsStochasticC (sweep H C) ∧ IsStationaryC (sweep H C) (posterior H C) := by sorry

end NestedCRP
