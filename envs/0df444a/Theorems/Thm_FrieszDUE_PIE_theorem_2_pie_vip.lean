-- Prove2me | Theorems.Thm_FrieszDUE_PIE_theorem_2_pie_vip
-- name    : FrieszDUE.PIE.theorem_2_pie_vip
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:20:21.965292+00:00
-- url     : https://prove2.me/theorems/4882d1ab-de1e-458b-b5ae-fd775ae2f2bf
-- title:
--   Theorem 2 (PIE VIP), p. 187 — (h*, μ*) is a simultaneous route-departure equilibrium iff h* ∈ Λ solves Σ_p ∫ C_p(t, h*)[h_p − h*_p] dν ≥ 0 ∀ h ∈ Λ
-- statement:
--   Consider a traffic network with a finite set $P$ of paths, each connecting one origin–destination (OD) pair $kl$ ($P_{kl}$ the paths of pair $kl$), fixed demands $Q_{kl}$, and an analysis horizon $[0,T]$ with $T>0$ carrying Lebesgue measure $\nu$. A vector $h=(h_p)$ of departure-time densities lies in $\Lambda$ (38) if each $h_p$ is square-integrable and $\nu$-a.e. nonnegative and $\sum_{p\in P_{kl}}\int_0^T h_p\,d\nu=Q_{kl}$ for every OD pair. A cost operator assigns to each path $p$, time $t$ and $h$ the effective delay $C_p(t,h)$ of (13).
--
--   Let $h^*$ be a density vector whose costs $C_p(\cdot,h^*)$ are nonnegative on $[0,T]$ and square-integrable. Then:
--
--   1. (Necessity) if $(h^*,\mu^*)$ is a simultaneous route-departure equilibrium (Definition 3) for some vector $\mu^*$, then $h^*$ solves the variational inequality: $h^*\in\Lambda$ and
--   $$\sum_{p\in P}\int_0^T C_p(t,h^*)\,[h_p(t)-h^*_p(t)]\,d\nu(t)\ge 0\qquad\text{for all }h\in\Lambda;\qquad(39)$$
--   2. (Sufficiency) if $h^*$ solves (39), then $(h^*,\mu^*)$ with $\mu^*_{kl}=\mu_{kl}(h^*)$ — the minimum over $p\in P_{kl}$ of the essential infimum of $C_p(\cdot,h^*)$ on $[0,T]$ — is a simultaneous route-departure equilibrium.
--
--   In particular, the simultaneous route-departure equilibrium problem is equivalent to the variational inequality (39) on $\Lambda$. This is the paper's main result: it recasts dynamic user equilibrium in route and departure-time choice as an infinite-dimensional variational inequality in $(L^2[0,T])^{|P|}$.
--
--   **Formalization Note** The cost operator $C$ is abstract. The paper's measurability assumption on $C_p(\cdot,h)$ is strengthened to square-integrability, and both it and nonnegativity are assumed only at $h^*$ (which makes the statement stronger than the paper's, where they hold for every $h\in H_+$). Square-integrability is needed because Lean's integral of a non-integrable function is $0$, which would let (39) hold vacuously.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 187, Theorem 2 (PIE VIP) and (39); proof pp. 187–189

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Theorem 2 (PIE VIP), p. 187. -/
theorem theorem_2_pie_vip {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (hT : 0 < T) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ)
    (hC_nonneg : ∀ p, ∀ t ∈ Set.Icc 0 T, 0 ≤ C p t hs)
    (hC_L2 : ∀ p, MemLp (fun t => C p t hs) 2 (ν T)) :
    (∀ mu : W → ℝ, IsSRDEquilibrium T od Q C hs mu → IsPIEVISolution T od Q C hs) ∧
      (IsPIEVISolution T od Q C hs → IsSRDEquilibrium T od Q C hs (muOD T od C hs)) := by sorry

end FrieszDUE.PIE
