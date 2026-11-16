-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_parallel_simulation
-- name    : MatchingNearLinear.Glauber.Supplement.parallel_simulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:27.612201+00:00
-- url     : https://prove2.me/theorems/e98c2696-918f-4884-bf2b-795641edc238
-- title:
--   Theorem 5.1 — Work-efficient parallel simulation
-- statement:
--   There are a deterministic CREW PRAM program $B$, a word-capacity exponent $r$, an absolute exponent $k$ and an absolute constant $C>0$ such that the following holds. Let $G$ be a labeled simple graph with $n$ vertices, $m\ge1$ edges, maximum degree $\Delta$ and maximum matching size $r_G=\nu(G)$; let $\lambda_e>0$ be arbitrary activities, $p_e=\lambda_e/(1+\lambda_e)$, $p^*=\max_ep_e$; let $N\ge1$ and let $M_0$ be any matching. $B$ receives the edge list, $\lambda$, $M_0$ and an update tape $(e_s,B_s)_{s=1}^N$, with words below $(n+m+N+2)^{r+1}$.
--
--   1. **Exactness.** On every tape, $B$ halts and outputs the matching returned by the batch occupation-interval algorithm ($\lceil N/m\rceil$ consecutive batches of at most $m$ updates). When the tape has independent pairs with $e_s$ uniform and $B_s\mid e_s=e\sim\mathrm{Ber}(p_e)$, this output has exactly the law of $N$ random-scan single-edge GD updates from $M_0$:
--   $$\Pr[\text{output}=S]=P_{GD}^N(M_0,S)\qquad\text{for every matching }S.$$
--   2. **Work.** For every $0<\eta\le1/4$, with $S=(m+n+N+10)/\eta$, the work is at most $C(m+n+N)\log^kS$ on every tape.
--   3. **Depth.** For every $0<\eta\le1/4$, with probability at least $1-\eta$ over the tape, the depth is at most
--   $$C\Big(1+\frac Nm\Big)\big(1+\min\{p^*\Delta,\sqrt{p^*r_G}\}\big)\log^kS .\qquad(28)$$
--
--   The simulation is exact; $\eta$ only controls the stated depth bound. Substituting the near-linear mixing horizon yields the parallel sampler of Theorem 1.2.
--
--   Differences from the source:
--
--   - encoding: the batch algorithm, a randomized CREW algorithm whose randomness is the generated update tape → a deterministic CREW.Program that receives the update tape in memory; probabilities are over the tape law; reason: the algorithm uses no randomness besides the tape (§5.1), and its implementation (Lemma 5.6) is deterministic on every update sequence; drawing the tape costs O(N) work and O(1) depth
--   - encoding: work and depth (m+n+N) log^{O(1)} S and (28) with log^{O(1)} S → C·(…)·(log S)^k with one absolute exponent k and constant C chosen before every instance and every η; reason: the theorem has no parameter besides the instance
--   - encoding: exactly simulates N random-scan single-edge GD updates from any given matching → output equals the batch algorithm on every tape, and the output law equals row M_0 of the N-th power of the single-edge heat-bath kernel on the support of μ_{G,λ}; M_0 ranges over that support (the matchings); reason: the support of μ_{G,λ} is exactly the set of matchings for positive activities
--   - encoding: depth of the run → depth of the run with a fixed randomness sequence; reason: a deterministic program draws no random choice, so the run does not depend on it
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Theorem 5.1 and Eq. (28), printed p. 22 (PDF p. 24); algorithm §5.1, printed pp. 22–23 (PDF pp. 24–25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_Programs
import Definitions.Def_MatchingNearLinear_Glauber_Sampler

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber
open Classical

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem parallel_simulation :
    ∃ (B : CREW.Program) (r k : ℕ) (C : ℝ), 0 < C ∧ B.Deterministic ∧
      ∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ), (∀ e, 0 < lam e) →
      ∀ N : ℕ, 1 ≤ N → ∀ M0 : Support (matchingLaw G lam),
        let cap := CREW.capacity (n + m + N) r
        (∀ (tape : Fin N → Fin m × Bool) (ω : CREW.Randomness), ∃ t c,
          CREW.HaltsAt B cap (simulationInput G lam M0.val tape) ω t c ∧
          OutputsConfig m c (batchOutput G M0.val tape)) ∧
        (∀ S : Support (matchingLaw G lam),
          (∑ tape : Fin N → Fin m × Bool,
            if batchOutput G M0.val tape = S.val then tapeWeight lam tape else 0) =
          ((subsetGlauber (matchingLaw G lam))^N) M0 S) ∧
        ∀ η : ℝ, 0 < η → η ≤ 1/4 →
          let S := ((m : ℝ) + n + N + 10) / η
          (∀ (tape : Fin N → Fin m × Bool) (ω : CREW.Randomness) t c,
            CREW.HaltsAt B cap (simulationInput G lam M0.val tape) ω t c →
            (c.work : ℝ) ≤ C * ((m : ℝ) + n + N) * (Real.log S)^k) ∧
          1 - η ≤ ∑ tape : Fin N → Fin m × Bool,
            if ∃ t c, CREW.HaltsAt B cap (simulationInput G lam M0.val tape) (fun _ => 0) t c ∧
                (t : ℝ) ≤ C * (1 + (N : ℝ) / m) *
                  (1 + min (maxMarkProb lam * maxDegree G)
                    (Real.sqrt (maxMarkProb lam * maxMatchingSize G))) * (Real.log S)^k
            then tapeWeight lam tape else 0 := by sorry

end MatchingNearLinear.Glauber.Supplement
