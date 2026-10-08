-- Prove2me | Theorems.Thm_FrieszDUE_PIE_theorem_2_sufficiency
-- name    : FrieszDUE.PIE.theorem_2_sufficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:20:16.806194+00:00
-- url     : https://prove2.me/theorems/4458a829-aeaf-4cd7-8650-b2ada7098a34
-- title:
--   Theorem 2 part ii (Sufficiency), pp. 187–189 — a solution h* of the VI (39) gives the SRD equilibrium (h*, μ(h*))
-- statement:
--   In the setting of the PIE model, let $T>0$ and let $h^*$ be a density vector whose costs $C_p(\cdot,h^*)$ are nonnegative on $[0,T]$ and square-integrable. If $h^*\in\Lambda$ solves the variational inequality
--
--   $$\sum_{p\in P}\int_0^T C_p(t,h^*)\,[h_p(t)-h^*_p(t)]\,d\nu(t)\ge 0\qquad\text{for all }h\in\Lambda,\qquad(39)$$
--
--   then, with $\mu^*_{kl}=\mu_{kl}(h^*)$ the minimal essential-infimum cost (15), the pair $(h^*,\mu^*)$ is a simultaneous route-departure equilibrium (Definition 3).
--
--   This is the sufficiency half of Theorem 2 (PIE VIP); it identifies the equilibrium cost levels explicitly as the essential infima $\mu_{kl}(h^*)$.
--
--   **Formalization Note** The square-integrability of $C_p(\cdot,h^*)$ strengthens the paper's measurability assumption so that every integral in (39) is a genuine Lebesgue integral.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), pp. 187–189, Theorem 2 part ii (Sufficiency), (44)–(54)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Theorem 2 part ii (sufficiency), pp. 187–189. -/
theorem theorem_2_sufficiency {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (hT : 0 < T) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ)
    (hC_nonneg : ∀ p, ∀ t ∈ Set.Icc 0 T, 0 ≤ C p t hs)
    (hC_L2 : ∀ p, MemLp (fun t => C p t hs) 2 (ν T)) :
    IsPIEVISolution T od Q C hs → IsSRDEquilibrium T od Q C hs (muOD T od C hs) := by sorry

end FrieszDUE.PIE
