-- Prove2me | Theorems.Thm_MatchingNearLinear_Glauber_Supplement_interval_peeling_depth
-- name    : MatchingNearLinear.Glauber.Supplement.interval_peeling_depth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:01:25.287206+00:00
-- url     : https://prove2.me/theorems/65795cf3-a24c-4311-bb40-8580d2189313
-- title:
--   Lemma 5.3 — Depth of interval peeling
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a labeled simple graph with $n$ vertices, $m\ge1$ edges, maximum degree $\Delta$ and maximum matching size $\nu(G)$; let $\lambda_e>0$ be arbitrary edge activities (no upper bound), $p_e=\lambda_e/(1+\lambda_e)$ and $p^*=\max_ep_e$. Let $M_0$ be any fixed input matching, $T\le m$, $0<\xi\le1/4$, and $S_b=(m+n+T+10)/\xi$. Draw a batch of $T$ independent updates $(e_s,B_s)$, with $e_s$ uniform over the $m$ edges and $B_s\mid e_s=e\sim\mathrm{Ber}(p_e)$, and let $R$ be the number of peeling rounds (after the initial step) of the occupation-interval algorithm. Then
--   $$\Pr\Big[R\le C\big(1+\min\{p^*\Delta,\sqrt{p^*\nu(G)}\}\big)\log^3S_b\Big]\ \ge\ 1-\xi .$$
--
--   This is the depth half of the work-efficient parallel simulation (Theorem 5.1).
--
--   Differences from the source:
--
--   - encoding: R = O((1 + min{p*Δ, √(p*ν(G))}) log³ S_b) with probability at least 1 − ξ → one absolute C>0, chosen before every graph, activity vector, matching, T and ξ; the probability is the sum of the tape law over tapes satisfying the bound; reason: the O hides an absolute constant (the lemma has no other parameter)
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), Lemma 5.3 and Eq. (29), printed p. 23 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_Supplement_Peeling
import Definitions.Def_MatchingNearLinear_Glauber_Sampler

set_option autoImplicit false

namespace MatchingNearLinear.Glauber.Supplement

open MatchingNearLinear.Glauber

/-- Tianshun Miao and Yitong Yin, Sampling Matchings in Near-linear Time,
STOC 2027 submission #444 (October 2026). Exact result and pages in the item metadata. -/
theorem interval_peeling_depth :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ), 1 ≤ m → ∀ (G : Input n m) (lam : Fin m → ℝ), (∀ e, 0 < lam e) →
      ∀ M0 : Config m, EdmondsMatching65.Polyhedron.IsMatching G.graph M0 →
      ∀ T : ℕ, T ≤ m → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1/4 →
        let Sb := ((m : ℝ) + n + T + 10) / ξ
        1 - ξ ≤ ∑ tape : Fin T → Fin m × Bool,
          if (peelRounds G M0 tape : ℝ) ≤
              C * (1 + min (maxMarkProb lam * maxDegree G)
                (Real.sqrt (maxMarkProb lam * maxMatchingSize G))) * (Real.log Sb)^3
          then tapeWeight lam tape else 0 := by sorry

end MatchingNearLinear.Glauber.Supplement
