-- Prove2me | Theorems.Thm_MarkovInterference_DQBias_theorem_1
-- name    : MarkovInterference.DQBias.theorem_1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:46.59481+00:00
-- url     : https://prove2.me/theorems/0bf87113-21b9-4f9f-ba10-70848955701e
-- title:
--   Theorem 1 — second-order bias of the idealized DQ estimator
-- statement:
--   Consider a finite two-action Markov decision process. The control and intervention transition matrices are primitive, with stationary laws $\rho_0$ and $\rho_1$; the half-randomized experiment has stationary law $\rho_{1/2}$. Suppose $0<\lambda<1$ and, for every state $s$ and $k\ge0$,
--
--   $$d_{\mathrm{TV}}(P_{1/2}^k(s,\cdot),\rho_{1/2})\le C\lambda^k.$$
--
--   If $d_{\mathrm{TV}}(P_1(s,\cdot),P_0(s,\cdot))\le\delta$ at every state, then a single real polynomial $q$, independent of the MDP and all its parameters, satisfies
--
--   $$\left|\mathrm{ATE}-\mathbb E_{\rho_{1/2}}[\widehat{\mathrm{ATE}}_{\mathrm{DQ}}]\right|\le q(\log C)\left(\frac1{1-\lambda}\right)^2 r_{\max}\delta^2.$$
--
--   The result gives a second-order bound on the population bias of differences-in-Q in the intervention's effect on transitions.
--
--   **Formalization Note** Primitivity of $P_0,P_1$ encodes the §2 ergodic-policy convention; $0<\lambda<1$ makes the paper's denominators and logarithmic mixing rate meaningful. The universal polynomial precedes every model quantifier. For a one-state chain the bias is zero even if $C=0$. This stationary average-reward setting differs from finite-horizon treatment-effect estimators elsewhere in the catalog.
-- source:
--   Farias, Li, Peng, Zheng, Markovian Interference in Experiments, arXiv:2206.02371v2, p. 12, Theorem 1; pp. 9–11, §2 and Assumption 1

import Mathlib
import Definitions.Def_MarkovInterference_DQBias_Chain
import Definitions.Def_MarkovInterference_DQBias_MDP

namespace MarkovInterference.DQBias

/-- Theorem 1, p. 12: second-order bias for the idealized differences-in-Q estimator. -/
theorem theorem_1 :
    ∃ q : Polynomial ℝ, ∀ {S : Type} [Fintype S] [DecidableEq S] (M : MDP S)
      (rhoHalf rho0 rho1 : S → ℝ) (C lam δ : ℝ),
      IsPrimitive (M.P 0) → IsPrimitive (M.P 1) →
      IsStationaryDist M.Phalf rhoHalf →
      IsStationaryDist (M.P 0) rho0 → IsStationaryDist (M.P 1) rho1 →
      0 < lam → lam < 1 →
      (∀ (k : ℕ) (s : S), tvDist ((M.Phalf ^ k) s) rhoHalf ≤ C * lam ^ k) →
      (∀ s : S, tvDist (M.P 1 s) (M.P 0 s) ≤ δ) →
      |M.ate rho0 rho1 - M.dqMean rhoHalf| ≤
        q.eval (Real.log C) * (1 / (1 - lam)) ^ 2 * M.rmax * δ ^ 2 := by sorry

end MarkovInterference.DQBias
