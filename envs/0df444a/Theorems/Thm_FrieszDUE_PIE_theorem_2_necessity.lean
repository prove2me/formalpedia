-- Prove2me | Theorems.Thm_FrieszDUE_PIE_theorem_2_necessity
-- name    : FrieszDUE.PIE.theorem_2_necessity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:19:25.104735+00:00
-- url     : https://prove2.me/theorems/243154d2-391d-4358-82f9-dc5ba42e4e0a
-- title:
--   Theorem 2 part i (Necessity), p. 187 — an SRD equilibrium (h*, μ*) gives a solution h* of the VI (39)
-- statement:
--   In the setting of the PIE model (horizon $T$, paths $P$, OD map, demands $Q$, Lebesgue measure $\nu$ on $[0,T]$, feasible set $\Lambda$ of (38)), let $C$ be a cost operator and $h^*$ a density vector such that each cost $C_p(\cdot,h^*)$ is square-integrable on $[0,T]$. If $(h^*,\mu^*)$ is a simultaneous route-departure equilibrium (Definition 3) for some vector $\mu^*$, then $h^*\in\Lambda$ and
--
--   $$\sum_{p\in P}\int_0^T C_p(t,h^*)\,[h_p(t)-h^*_p(t)]\,d\nu(t)\ge 0\qquad\text{for all }h\in\Lambda.$$
--
--   This is the necessity half of Theorem 2 (PIE VIP): every equilibrium solves the variational inequality.
--
--   **Formalization Note** The square-integrability of $C_p(\cdot,h^*)$ is added to the paper's measurability assumption so that every integral in (39) is a genuine Lebesgue integral; Lean's Bochner integral of a non-integrable function is $0$.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 187, Theorem 2 part i (Necessity), (39)–(43)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Theorem 2 part i (necessity), p. 187. -/
theorem theorem_2_necessity {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ)
    (hC_L2 : ∀ p, MemLp (fun t => C p t hs) 2 (ν T)) :
    ∀ mu : W → ℝ, IsSRDEquilibrium T od Q C hs mu → IsPIEVISolution T od Q C hs := by sorry

end FrieszDUE.PIE
