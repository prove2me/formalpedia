-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_Supplement_theorem_6
-- name    : OnlineMatchFrameworks.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:28:11.737277+00:00
-- url     : https://prove2.me/theorems/a749fdf3-9bc2-4021-9531-c8b3fdb69af5
-- title:
--   Theorem 6: the LP (5) algorithm is a $1/2$-approximation for an arbitrary patience distribution
-- statement:
--   A single customer is offered items from a finite set $U$ of size $m$, with probabilities $p_j$ and weights $w_j\ge0$. The patience of the customer follows a known distribution, given by its tail $q_\theta=\Pr[\text{patience}\ge\theta]$ with $q_1=1$. For every optimal solution $x^*$ of LP (5), the randomized algorithm that chooses item $j$ at attempt $\theta$ with probability $x^*_{j\theta}/s^*_\theta$, and simulates the probe of an item probed before, has expected reward
--
--   $$
--   \mathrm{ALG}\ \ge\ \frac12\,\mathrm{OPT}(U,v),
--   $$
--
--   where $\mathrm{OPT}(U,v)$ is the best expected reward of a strategy that does not know the realized patience. So the single-customer problem with unknown patience has a $1/2$-approximation, usable as a black box with $\kappa=1/2$.
--
--   Differences from the source:
--   - encoding: the optimal strategy of a single customer without knowledge of the patience → the published star optimum, the maximum over duplicate-free lists; reason: the only feedback while the customer is present is a failure, so lists are all the deterministic strategies (p.16)
--   - generalization: patience with finite support in [m], without loss of generality (p.23) → any tail, with possibly infinite support; reason: a patience in [m] is a special case; only q_1, …, q_m matter
--   - encoding: patience at least 1, since customers of patience 0 are ignored (p.23, "1 = q_1") → q 1 = 1; reason: the paper’s own normalization; monotonicity and nonnegativity of q are those of the instance’s survival function
--   - reading: choose j with probability x*_{jθ}/s*_θ; a simulated probe ends the process on success (p.25); the empty choice and patience are not described → an empty choice and a simulated probe each use one attempt, and there are m attempts; reason: the proof uses Pr[attempt θ is reached] = s*_θ (pp.43–44); real probes alone can only reach each first probe more often, so this is the stronger reading
--   - reading: choose j = 1, …, n (p.25) → j ranges over the m items; reason: n is a misprint for m in §5.2 (LP (5) sums j to m)
--   - reading: an optimal solution x* of LP (5) → every optimal solution; reason: the algorithm does not say which one is found
--   - reading: weights of edges (p.11), no sign stated → w ≥ 0; reason: weights are prices and rewards; this is the standing convention of the paper and of the published mission
--   - encoding: 1/2-approximation → 1/2·OPT ≤ ALG; reason: covers OPT = 0 and is equivalent otherwise
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Theorem 6, p.26

import Definitions.Def_OnlineMatchFrameworks_Supplement_PatienceRounding
import Definitions.Def_OnlineMatchFrameworks_PatienceModels

namespace OnlineMatchFrameworks.Supplement

/-- **Theorem 6.** arXiv:1907.03963v6, Theorem 6, p.26: "The online algorithm based on LP (5) is a
1/2-approximation for the star graph probing problem, for an arbitrary patience distribution which is
given explicitly."

**Formalization Note.** `q θ = Pr[patience ≥ θ]`, with `q 1 = 1` (p.23); the instance's survival
function is the published `tailSurvival` of `q`, whose monotonicity is part of `Instance`. Every
antitone nonnegative `q` with `q 1 = 1` gives such an instance, and the support may be infinite. The
benchmark is the optimal star value without knowledge of the patience (Theorem 10 shows that a
clairvoyant cannot be matched). `x` is any optimal solution of LP (5). -/
theorem theorem_6 {U : Type*} [Fintype U] [DecidableEq U]
    (G : OnlineMatchFrameworks.Instance U Unit) (q : ℕ → ℝ) (hq1 : q 1 = 1)
    (hS : ∀ l, G.surv () l = OnlineMatchFrameworks.tailSurvival (fun _ => q) () l)
    (x : U → ℕ → ℝ) (hx : IsPatienceOptimal G q x) :
    1 / 2 * G.starOpt Finset.univ () ≤ patienceALG G q x := by sorry

end OnlineMatchFrameworks.Supplement
