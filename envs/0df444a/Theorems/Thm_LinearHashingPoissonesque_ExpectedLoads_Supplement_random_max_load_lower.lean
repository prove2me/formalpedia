-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_random_max_load_lower
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.random_max_load_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:07:23.061035+00:00
-- url     : https://prove2.me/theorems/8cc73f7c-eeb5-4a4f-a074-05c81a6c8aea
-- title:
--   Lemma 5 (used in the proof of Theorem 2) — fully random maximum-load lower bound
-- statement:
--   For each positive integer $n$, let $m(n)\ge1$ be an integer and let $0<\eta(n)\le1$. Put $\mu(n)=m(n)/n$, $t(n)=T_1^+(m(n),n)$, and let $R(m,n)$ be the expected maximum load of a uniformly random function $[m]\to[n]$. If
--
--   $$\frac{(t(n)/\mu(n))^{\eta(n)}}{\sqrt{\mu(n)}\log(e+t(n))}\longrightarrow+\infty,$$
--
--   then there is a real sequence $e_n\to0$ such that, for all sufficiently large $n$,
--
--   $$R(m(n),n)\ge\left\lfloor t(n)-\tfrac12-\eta(n)\right\rfloor-e_n.$$
--
--   The floor encloses the entire expression $t-1/2-\eta$. This is the fully random lower estimate used in the additive comparison of Theorem 2.
--
--   Differences from the source:
--   - encoding: Definition 1 real Poisson thresholds → published upperThreshold and lowerThreshold, using their root sets and exact zero branch; reason: on positive real m and 1 ≤ r ≤ n the nonzero root sets are singletons; no rounding or extra hypothesis is imposed
--   - encoding: positive integer arguments n and m(n), implicit from Definition 1 and uniform nonempty bins → natural sequences with m(n) ≥ 1 and eta(n) in (0,1] for n ≥ 1; reason: the value at n=0 has no effect on an atTop limit or eventual conclusion
--   - encoding: a limit to infinity and an additive o(1) remainder → Tendsto atTop atTop and an existential null sequence with an eventual inequality; reason: these express the same asymptotic statements and do not assert a bound at finitely many small n
--   - encoding: uniform functions on one-based finite labels and an integer floor → fullyRandomMaxLoad on Fin m → Fin n and the real cast of Int.floor; reason: relabeling preserves loads and every function; the entire t-1/2-eta expression remains under the floor
--   - encoding: T^+(m,n) written without a subscript → upperThreshold (m n) n 1, the r = 1 threshold; reason: the paper's own use in the proof of Theorem 2 sets t = T_1^+(n,n), and p.16 identifies T^+(n,n) with the r = 1 root of t log t − t + 1 = log n
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.17, Lemma 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=17

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_Supplement_FullyRandomMaxLoad

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

open Filter Topology in
/-- Lemma 5, p.17: the integer floor and an eventual additive null error. -/
theorem random_max_load_lower (m : ℕ → ℕ) (eta : ℕ → ℝ)
    (hm : ∀ n : ℕ, 1 ≤ n → 1 ≤ m n)
    (heta : ∀ n : ℕ, 1 ≤ n → 0 < eta n ∧ eta n ≤ 1)
    (hlim : Tendsto
      (fun n : ℕ =>
        (upperThreshold (m n : ℝ) n 1 / ((m n : ℝ) / n)) ^ (eta n) /
          (Real.sqrt ((m n : ℝ) / n) *
            Real.log (Real.exp 1 + upperThreshold (m n : ℝ) n 1))) atTop atTop) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (⌊upperThreshold (m n : ℝ) n 1 - (1 : ℝ) / 2 - eta n⌋ : ℝ) - e n ≤
          fullyRandomMaxLoad (m n) n := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
