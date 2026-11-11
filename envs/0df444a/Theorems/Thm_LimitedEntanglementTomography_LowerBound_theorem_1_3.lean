-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_theorem_1_3
-- name    : LimitedEntanglementTomography.LowerBound.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:03.080901+00:00
-- url     : https://prove2.me/theorems/937397cf-d836-44dc-801d-ff09f1e22b55
-- title:
--   Theorem 1.3 — tight lower bound for tomography with measurements on at most $k$ copies
-- statement:
--   There are absolute constants $\varepsilon_0>0$ and $c>0$ such that the following holds. For every $d\ge2$, every integer $k\ge1$ and every $0<\varepsilon\le\varepsilon_0$, any protocol of Definition 1.1 that solves Problem 1.2 using at most $n$ copies satisfies
--   $$n\ge c\,\frac{d^3}{\varepsilon^2\sqrt{\min\{k,d^2\}}}=c\,\max\Big\{\frac{d^3}{\sqrt k\,\varepsilon^2},\ \frac{d^2}{\varepsilon^2}\Big\}.$$
--
--   Here a protocol measures, in each round, a joint POVM on $t_j\le k$ fresh copies chosen adaptively from its internal randomness and all previous classical outcomes; it may stop at a random time, and $\sum_jt_j\le n$ almost surely under every state. Solving Problem 1.2 means producing a state within trace distance $\varepsilon$ of the unknown state with probability at least $2/3$, for every state. The bound covers adaptive measurements and nonuniform or random block sizes.
--
--   At $k=1$ it is the single-copy rate $d^3/\varepsilon^2$, and for $k\ge d^2$ it is the unrestricted rate $d^2/\varepsilon^2$.
--
--   Differences from the source:
--   - encoding: Definition 1.1: rounds j = 1,…,T with 1 ≤ t_j ≤ k, a random stopping time, Σ t_j ≤ n almost surely → a protocol has a horizon `rounds`; a round with t_j = 0 makes no measurement (this encodes stopping); the outcome kernels are part of the data and are pinned to the Born laws on every state; Σ t_j ≤ n almost surely under every state; one standard Borel outcome space Out serves every round, and the POVM effects are measurable in the whole history; reason: T ≤ n since active rounds use at least one copy, so a horizon loses nothing; a round with t_j = 0 followed by measuring rounds is equivalent to the same protocol without that round, so the class of experiments is unchanged; the kernel exists and is unique on states for every source protocol; every standard Borel outcome space embeds Borel-isomorphically into one (for instance into ℝ), and a POVM family measurable on the histories with t_j = t extends to all histories by a fixed POVM
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §1.1, printed p.2 / PDF p.4, Theorem 1.3 (eq. (1)); restated and proved in §5, printed pp.19–20 / PDF pp.21–22

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Protocol

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Theorem 1.3, printed p.2 / PDF p.4, eq. (1); repeated printed p.19 / PDF p.21.
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Theorem 1.3.** There are absolute constants `ε₀ > 0` and `c > 0` such that for every
`d ≥ 2`, every integer `k ≥ 1`, every `0 < ε ≤ ε₀` and every `n`, every protocol of
Definition 1.1 (adaptive, measurements on at most `k` fresh copies, at most `n` copies almost
surely) with an estimator solving Problem 1.2 (trace distance `≤ ε` with probability `≥ 2/3` on
every state) has `n ≥ c · d³ / (ε² √(min{k, d²}))`, equivalently
`n ≥ c · max{d³/(√k ε²), d²/ε²}`. -/
theorem theorem_1_3 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (d : ℕ), 2 ≤ d → ∀ (k : ℕ), 1 ≤ k → ∀ (ε : ℝ), 0 < ε → ε ≤ ε₀ →
      ∀ (n : ℕ) (P : Protocol d k) (est : P.Estimator), P.UsesAtMost n → P.Solves est ε →
        c * ((d : ℝ) ^ 3 / (ε ^ 2 * Real.sqrt (min (k : ℝ) ((d : ℝ) ^ 2)))) ≤ n ∧
        c * max ((d : ℝ) ^ 3 / (Real.sqrt k * ε ^ 2)) ((d : ℝ) ^ 2 / ε ^ 2) ≤ n := by sorry

end LimitedEntanglementTomography.LowerBound
