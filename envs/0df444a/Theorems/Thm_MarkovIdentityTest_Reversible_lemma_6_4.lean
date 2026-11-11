-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_6_4
-- name    : MarkovIdentityTest.Reversible.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:38:08.052195+00:00
-- url     : https://prove2.me/theorems/9aab8bb7-64df-4b35-9264-92b3504847dd
-- title:
--   Lemma 6.4 — the occupation energy is $O(n)$ under the reference: $\mathbb E_{P,x}O_P(N)\le 24n$
-- statement:
--   Let $P$ be stochastic and reversible with respect to some strictly positive probability vector, and let $T$ be an independent positive geometric time of mean $M\ge2$. Then for every initial state $x$, with $N$ the departure-count vector of the trajectory up to $T$, $O_P(N)$ is integrable and
--   $$\mathbb E_{P,x}O_P(N)\le24n .$$
--   No minimum stationary probability enters the bound.
--
--   Differences from the source:
--
--   - generalization: M = ⌈C₀ n/ε⌉ with C₀ large (so M ≥ 2) → any real M ≥ 2; reason: the proof uses only z = 1 − 1/M ≥ 1/2; specializes
--   - encoding: E_{P,x} at the geometric deadline → series over t with absolute convergence asserted; reason: rules out a default value 0
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 35, Lemma 6.4

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Discrepancy
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- Lemma 6.4 (Jia, p. 35 / PDF 37): for a reversible reference `P`, at the geometric deadline
`T` of mean `M ≥ 2`, `E_{P,x} O_P(N) ≤ 24n` from every initial state. -/
theorem lemma_6_4 {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsStochastic P)
    (hrev : IsReversible P) (M : ℝ) (hM : 2 ≤ M) (x : Fin n) :
    GeomIntegrable M P x (fun _ ω => occupationEnergy P fun i => (departures ω i : ℝ)) ∧
      geomExp M P x (fun _ ω => occupationEnergy P fun i => (departures ω i : ℝ)) ≤ 24 * n := by sorry

end MarkovIdentityTest.Reversible
