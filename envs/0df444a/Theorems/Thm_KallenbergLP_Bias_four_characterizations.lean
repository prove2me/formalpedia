-- Prove2me | Theorems.Thm_KallenbergLP_Bias_four_characterizations
-- name    : KallenbergLP.Bias.four_characterizations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:18:04.452991+00:00
-- url     : https://prove2.me/theorems/68b3cebf-bce3-43ad-b5e0-90cf6a582211
-- title:
--   Theorem 5.2.2 — four equivalent characterizations of bias optimality
-- statement:
--   Let $f_*^\infty$ be a pure stationary policy in a finite stochastic Markov decision model. The following four statements are equivalent:
--
--   1. $f_*^\infty$ is bias optimal, comparing its discounted reward at every initial state with the value over **all** policies.
--   2. Against every pure stationary $f^\infty$ and at every initial state, the extended-real limit of $v_i^\beta(f_*^\infty)-v_i^\beta(f^\infty)$ as $\beta\uparrow1$ exists and is nonnegative. The value $+\infty$ is allowed when $f_*$ has strictly higher gain at that state.
--   3. $f_*^\infty$ is average optimal; at each state $i$, its bias $u_i(f_*^\infty)$ is at least that of every pure stationary $f^\infty$ with $\phi_i(f^\infty)=\phi_i$. The comparison class is chosen separately for each state.
--   4. Against every pure stationary $f^\infty$ and at every initial state, the following extended-real limit exists and is nonnegative (again allowing $+\infty$):
--
--   $$
--   \lim_{T\to\infty}\frac1T\sum_{t=1}^T\sum_{s=1}^t
--   \bigl(v_i^s(f_*^\infty)-v_i^s(f^\infty)\bigr)\ge0.
--   $$
--
--   The theorem converts the global, all-policy discounted definition of bias optimality into comparisons among the finite set of pure stationary policies, using either bias vectors or accumulated period rewards.
--
--   **Formalization Note** The printed clause (iii) has `max{u_i(f^∞) = φ_i}`; its proof on p. 164 specifies the intended restriction $\phi_i(f^\infty)=\phi_i$. Condition (iii) is encoded by attainment and an upper-bound inequality, avoiding a real `sSup` on a potentially empty displayed set. The formula's $v^s$ is a period reward, not a discounted value. The book's nonnegative limits in (ii) and (iv) are extended-real: if the gain gap is positive, their values are $+\infty$.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 164–165, Theorem 5.2.2 (clause (iii) read from its proof on p. 164); https://ir.cwi.nl/pub/13008

import Definitions.Def_KallenbergLP_Bias_Stationary

open Filter

namespace KallenbergLP.Bias

/-- Theorem 5.2.2 (pp. 164–165), with clause (iii) read as in its proof. -/
theorem four_characterizations {N : ℕ} {α : Type}
    [Fintype α] [DecidableEq α] (M : MDP N α) (fStar : PureRule M) :
    [
      IsBiasOptimal M (purePolicy M fStar),
      (∀ (f : PureRule M) (i : Fin N),
        ∃ L : EReal,
          Tendsto (fun β : ℝ =>
            ((discountedReward M (purePolicy M fStar) i β -
              discountedReward M (purePolicy M f) i β : ℝ) : EReal))
            (nhdsWithin 1 (Set.Iio 1)) (nhds L) ∧ 0 ≤ L),
      ((∀ i : Fin N, gain M fStar i = optimalAverage M i) ∧
        ∀ (i : Fin N) (f : PureRule M),
          gain M f i = optimalAverage M i → bias M f i ≤ bias M fStar i),
      (∀ (f : PureRule M) (i : Fin N),
        ∃ L : EReal,
          Tendsto (fun T : ℕ => (cesaroRewardDifference M fStar f i T : EReal))
            atTop (nhds L) ∧ 0 ≤ L)
    ].Pairwise (· ↔ ·) := by sorry

end KallenbergLP.Bias
