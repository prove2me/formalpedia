-- Prove2me | Theorems.Thm_HamLocality237_Testing_locality_testing_lower_bound
-- name    : HamLocality237.Testing.locality_testing_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:57.732896+00:00
-- url     : https://prove2.me/theorems/754e6298-441d-4474-bfff-eb74745fc542
-- title:
--   Corollary 4.2 — total forward evolution time for locality testing
-- statement:
--   There is an absolute real constant $c>0$ such that the following holds for every $n,k\in\mathbb N_0$ and $\varepsilon\in\mathbb R$ with $0<\varepsilon<1/4$, $8k\le n$, and $n\ge7$.
--
--   Let $A$ be any finite adaptive experiment protocol with forward time-evolution access. Suppose that for every Hermitian $n$-qubit $H$ of operator norm at most one, the protocol outputs local with probability at least $9/10$ when $H$ is $k$-local and far with probability at least $9/10$ when $\operatorname{dist}(H,k\text{-local})>\varepsilon$. If every positive-probability transcript on every promise input has total evolution time at most $T$, then
--
--   $$T\ge c\min\left\{\frac1{\varepsilon^2},\frac{2^{n/2}}\varepsilon\right\}.$$
--
--   The constant precedes every dimension, threshold, locality parameter, and protocol. The distance uses the normalized Frobenius norm. The protocol may use arbitrary mixed preparations, finite ancillas, input-independent interleaved unitaries, arbitrary nonnegative real query times, and classical adaptivity. This is the paper's locality-testing lower bound, including its dimension-dependent high-precision regime; it is not restricted to diagonal inputs or continuous-time algorithms. The statement is an open formalization target, not a proved Lean theorem.
--
--   Differences from the source:
--   - generalization: k is a positive natural number → k=0 is also allowed; reason: Lemma 4.1 includes k=0 and the same reduction applies; n≥7 is retained explicitly
--   - generalization: time is bounded over all input Hamiltonians and measurement outcomes → time is bounded only on promise inputs and positive-probability transcripts; reason: pruning branches unreachable by every promise input within the bound preserves all promise-input output probabilities
--   - encoding: n qubits, finite ancillary registers, real durations t_j≥0, and 2^(n/2) → Qubits n, Fin w ancillary bases, NNReal durations, and real exponentiation (2:ℝ)^((n:ℝ)/2); reason: finite bases enumerate the same experiment data and the exponent uses real division
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Corollary 4.2, p.24; proof continued p.25. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_Protocol

namespace HamLocality237.Testing

/-- Corollary 4.2, p.24. The absolute constant precedes every instance parameter.
Allows k=0 and charges only promise-reachable positive-probability transcripts. -/
theorem locality_testing_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (n k : ℕ) (ε : ℝ),
      0 < ε → ε < 1 / 4 → 8 * k ≤ n → 7 ≤ n →
      ∀ (A : Protocol n) (T : ℝ),
        A.TestsLocality k ε → A.HasPromiseTimeBound k ε T →
        c * min (1 / ε ^ 2) ((2 : ℝ) ^ ((n : ℝ) / 2) / ε) ≤ T := by sorry

end HamLocality237.Testing
