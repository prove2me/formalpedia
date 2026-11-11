-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_theorem_6_1
-- name    : MarkovIdentityTest.Reversible.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:38:13.260193+00:00
-- url     : https://prove2.me/theorems/e1775437-86ab-4514-b75e-418bc8e84fe8
-- title:
--   Theorem 6.1 — $\lceil C n/\varepsilon\rceil$ transitions test a reversible reference $P$ against every stochastic $Q$ with $\Delta(P,Q)\ge\varepsilon$, both errors $\le 1/3$
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $n\ge1$, let $P$ be a stochastic $n\times n$ matrix that is reversible with respect to some strictly positive probability vector $\pi$ ($\pi_iP_{ij}=\pi_jP_{ji}$), and let $0<\varepsilon\le1$. Put $m=\lceil Cn/\varepsilon\rceil$. Then there is a test $\varphi$ — a function from paths $(X_0,\dots,X_m)$ of $m$ transitions to $[0,1]$, the probability of rejecting — such that
--   $$\Pr_{P,x}(\text{reject})=\sum_\omega\Pr_{P,x}(\omega)\varphi(\omega)\le\tfrac13\quad\text{for every initial state }x,$$
--   and, for every stochastic $Q$ with $\Delta(P,Q)=1-\rho\big([\sqrt{P_{ij}Q_{ij}}]\big)\ge\varepsilon$ and every initial state $x$,
--   $$\Pr_{Q,x}(\text{accept})=\sum_\omega\Pr_{Q,x}(\omega)(1-\varphi(\omega))\le\tfrac13 .$$
--   The test depends on $n,\varepsilon,P$ only; $C$ depends on nothing. No irreducibility, aperiodicity or lower bound on $\pi$ is assumed, and $Q$ may be nonreversible, reducible or periodic.
--
--   This is the paper's headline result: identity testing of a reversible chain from one trajectory with $O(n/\varepsilon)$ transitions, matching the $\Omega(n/\varepsilon)$ lower bound of Daskalakis, Dikkala and Gravin.
--
--   Differences from the source:
--
--   - encoding: states [n] = {1, …, n} → Fin n with 0 < n; reason: 0-based indexing; [n] is nonempty
--   - encoding: a (randomized) test using at most ⌈C_rev n/ε⌉ transitions → φ : paths of exactly m = ⌈C n/ε⌉₊ transitions → [0, 1], the rejection probability, chosen from n, ε, P; reason: a test that stops earlier ignores the suffix; the test's own randomness (the geometric T) is averaged into φ; φ is not required to be {0,1}-valued, which would be a stronger claim
--   - encoding: reversible with respect to a strictly positive stationary distribution → ∃ π, π > 0, ∑ π = 1, π_i P_ij = π_j P_ji; reason: detailed balance for a stochastic P implies stationarity
--   - encoding: error probabilities as maxima over initial states (and over Q for type II) → bounds for every initial state x (and every Q); reason: a maximum over finitely many states is ≤ 1/3 iff each term is
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 31, Theorem 6.1 (proved in §6.4, pp. 35–36)

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- Theorem 6.1 (Jia, p. 31 / PDF 33). -/
theorem theorem_6_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 0 < n →
      ∀ (P : Matrix (Fin n) (Fin n) ℝ), IsStochastic P → IsReversible P →
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∃ φ : (Fin (⌈C * n / ε⌉₊ + 1) → Fin n) → ℝ,
        (∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1) ∧
        (∀ x : Fin n, rejectProb P x φ ≤ 1 / 3) ∧
        (∀ Q : Matrix (Fin n) (Fin n) ℝ, IsStochastic Q → ε ≤ discrepancy P Q →
          ∀ x : Fin n, acceptProb Q x φ ≤ 1 / 3) := by sorry

end MarkovIdentityTest.Reversible
