-- Prove2me | Theorems.Thm_MemQueryFeas_ap17_restart
-- name    : MemQueryFeas.ap17_restart
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:36:57.393206+00:00
-- url     : https://prove2.me/theorems/a625465c-fee3-44ae-87d1-ca1bb67b1da2
-- title:
--   Proof of Theorem 1, [AP17] step — restarting gives almost-sure success in expected $\le3(T+1)/2$ queries
-- statement:
--   Let a randomized $M$-bit algorithm solve feasibility problems of accuracy $\varepsilon$ within $T$ queries with probability at least $2/3$ against every valid measurable adaptive oracle. Then there is a randomized algorithm with $M+\lceil\log_2(T+1)\rceil$ bits of memory such that, against every (measurable) instance $Q$ of accuracy $\varepsilon$ and every valid measurable adaptive oracle, its first success time $\tau=\min\{t:x_t\in Q\}$ is finite almost surely and
--   $$
--   \mathbb E[\tau+1]\le\frac{3(T+1)}{2},
--   $$
--   $\tau+1$ being the number of queries up to and including the first feasible one.
--
--   The restarted algorithm repeats the original with fresh randomness without resetting the oracle; this turns the expected lower bound of (4.19) into the lower bound for algorithms succeeding with probability $2/3$.
--
--   Differences from the source:
--   - reading: the restarted algorithm (memory not discussed) → M + ⌈log₂(T+1)⌉ bits of memory; reason: restarting requires a round counter; any T at or above the bound of Theorem 1 already satisfies it, so the overhead is absorbed by the constants
--   - reading: expected query complexity → E[τ + 1], with τ the first round (0-based) whose query lies in Q; reason: the number of queries made until success
--   - reading: every valid adaptive separation oracle; every instance → valid measurable adaptive oracles and measurable instances Q; reason: almost-sure statements and expectations are defined when the first success time is a random variable
--   - generalization: Q contains a Euclidean ball of radius ε; success against every valid adaptive oracle → closed ε-ball; success hypothesis against measurable oracles only; reason: the same model as Theorem 1; a weaker hypothesis
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Proof of Theorem 1, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_MemQueryFeas_SucceedsAdaptive

open MeasureTheory
open scoped ENNReal

namespace MemQueryFeas

/-- **The restarting argument (proof of Theorem 1, [AP17] step).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), proof of Theorem 1, p.31
(PDF p.32): "a `T`-query algorithm with success probability at least `2/3` against every valid
adaptive separation oracle can be repeatedly restarted with fresh randomness (without resetting the
oracle), yielding an algorithm that succeeds almost surely with expected query complexity at most
`3(T + 1)/2`."

If a randomized `M`-bit algorithm succeeds within `T` queries with probability `2/3` against every
valid measurable adaptive oracle, then there is a randomized algorithm with `M + ⌈log₂(T+1)⌉` bits of
memory such that, against every instance `Q` (measurable) and every valid measurable adaptive oracle,
its first success time `τ` (first round `t` with `x_t ∈ Q`, `⊤` if none) is finite almost surely
and the expected number of queries `τ + 1` is at most `3(T + 1)/2`.

**Formalization Note.** The restarted algorithm needs a round counter, so it is given
`⌈log₂(T+1)⌉` (`Nat.clog 2 (T+1)`) extra bits. Rounds are 0-based, so the number of queries up to and
including the first success is `τ + 1`. The per-round draws are i.i.d. (`Measure.infinitePi`).
Probabilities and expectations are taken for measurable `Q` and measurable oracles, for which the
first success time is a random variable. -/
theorem ap17_restart {d M : ℕ} (ε : ℝ) (T : ℕ) (alg : RandMemAlg d M)
    (h : SucceedsAdaptive alg ε T) :
    ∃ alg' : RandMemAlg d (M + Nat.clog 2 (T + 1)),
      ∀ (Q : Set (Vec d)) (O : List (Vec d) → Vec d → Option (Vec d)),
        IsFeasInstance ε Q → MeasurableSet Q → IsValidAdaptive Q O → IsMeasurableAdaptive O →
        Measure.infinitePi (fun _ : ℕ => alg'.μ)
            {ω | ∀ t : ℕ, alg'.query (alg'.run O ω t).1 (ω t) ∉ Q} = 0 ∧
        ∫⁻ ω, ((((⨅ t ∈ {t : ℕ | alg'.query (alg'.run O ω t).1 (ω t) ∈ Q}, (t : ℕ∞)) + 1 : ℕ∞)) : ℝ≥0∞)
            ∂(Measure.infinitePi (fun _ : ℕ => alg'.μ)) ≤
          ENNReal.ofReal (3 * ((T : ℝ) + 1) / 2) := by sorry

end MemQueryFeas
