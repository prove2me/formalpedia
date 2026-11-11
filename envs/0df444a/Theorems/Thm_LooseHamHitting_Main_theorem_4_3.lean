-- Prove2me | Theorems.Thm_LooseHamHitting_Main_theorem_4_3
-- name    : LooseHamHitting.Main.theorem_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:52.625123+00:00
-- url     : https://prove2.me/theorems/2c7ab185-24ea-41b7-9cfa-57b790228cbf
-- title:
--   Theorem 4.3 — conditioned counting: log Φ(F∗) ≥ ((n∗ − s)/2) log(6m∗/n∗) − n∗ + s − C n∗/log n∗ with probability 1 − o(1)
-- statement:
--   There is an absolute constant $C>0$ such that, under Assumption 4.2, with probability $1-o(1)$,
--   $$\log\Phi(F_*)\ge\frac{n_*-s}2\log\frac{6m_*}{n_*}-n_*+s-C\frac{n_*}{\log n_*},$$
--   where $\Phi(F_*)=\Phi(F_*\cap K,M_0)$ and $F_*$ is uniform on $\Omega(n_*,m_*,\ell)$. The $o(1)$ term depends only on $n_*$: there is a null sequence $\varepsilon$ with failure probability at most $\varepsilon(n_*)$ for every instance of Assumption 4.2.
--
--   Theorem 1.1 follows from this statement applied conditionally on the exposure at $\tau_1$.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1), the o(1) depending only on n∗ → ∃ ε : ℕ → ℝ, ε → 0, failure probability ≤ ε(n∗) for every (m∗, ℓ, M₀) satisfying Assumption 4.2; reason: explicit null sequence
--   - encoding: log Φ(F∗) with log 0 = −∞ → failure event: Φ(F∗) = 0 or log Φ(F∗) below the bound; reason: the −∞ convention
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 14, Theorem 4.3

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Process
import Definitions.Def_LooseHamHitting_Main_Core

set_option autoImplicit false

open Classical Filter Topology

namespace LooseHamHitting.Main

/-- Theorem 4.3 (conditioned counting): an absolute constant `C` and a null sequence `ε` (a
function of `n∗` only) such that, under Assumption 4.2, `F∗ ∼ Unif Ω(n∗, m∗, ℓ)` fails
`log Φ(F∗) ≥ ((n∗ − s)/2) log(6m∗/n∗) − n∗ + s − C n∗/log n∗` with probability at most `ε n∗`
(`Φ(F∗) = 0` counts as a failure, `log 0 = −∞`). -/
theorem theorem_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ (n m : ℕ) (ℓ : Fin n → ℕ) (M₀ : Finset (Finset (Fin n))), CoreAssumption n m ℓ M₀ →
        uniformProb (Omega n m ℓ) (fun F => PhiCore n M₀ F = 0 ∨
          Real.log (PhiCore n M₀ F) <
            ((n : ℝ) - M₀.card) / 2 * Real.log (6 * (m : ℝ) / n) - n + M₀.card -
              C * n / Real.log n) ≤ ε n := by sorry

end LooseHamHitting.Main
