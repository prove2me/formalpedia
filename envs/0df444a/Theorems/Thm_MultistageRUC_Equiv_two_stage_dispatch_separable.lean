-- Prove2me | Theorems.Thm_MultistageRUC_Equiv_two_stage_dispatch_separable
-- name    : MultistageRUC.Equiv.two_stage_dispatch_separable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:07.031302+00:00
-- url     : https://prove2.me/theorems/68acbbef-9158-4fab-a1db-26d2893cf0ba
-- title:
--   Theorem 1, proof (i), first equality, p. 11 — the dispatch set without ramping is separable over time
-- statement:
--   Fix a commitment $x$ and a net-load trajectory $d=(d^1,\dots,d^T)$. Without ramping constraints the whole-horizon dispatch set is the product of the per-period sets $\Omega_t^{NR}(x,d^t)$ (generation limits (1h), line limits (1j), energy balance (1k)), so
--   $$\min_{\{p:\ p^t\in\Omega_t^{NR}(x,d^t)\ \forall t\in\mathcal T\}}\ \sum_{t\in\mathcal T}\sum_{i\in\mathcal N_g}C_ip_i^t=\sum_{t\in\mathcal T}\ \min_{p^t\in\Omega_t^{NR}(x,d^t)}\ \sum_{i\in\mathcal N_g}C_ip_i^t .$$
--
--   This is the first step of part (i) of the proof of Theorem 1, which reduces the two-stage model to problem (1P).
--
--   **Formalization Note** Minima are infima in the extended reals, $+\infty$ over an empty set. The identity is stated for every commitment and every trajectory; no uncertainty set is involved.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 11, Theorem 1, proof (i), first equality

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.Equiv

/-- Theorem 1, proof (i), first equality, p. 11: without ramping, the dispatch set
`{p : p^t ∈ Ω_t^{NR}(x, d^t) ∀ t}` is separable over time, so the least total dispatch cost for a
fixed net-load trajectory `d` is the sum over periods of the least per-period dispatch costs. -/
theorem two_stage_dispatch_separable {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (x u v : Fin Ng → Fin T → ℝ) (d : Fin T → Fin Nd → ℝ) :
    (⨅ p ∈ twoStageFeas D false x u v d, ((∑ t, dispCost D (p t) : ℝ) : EReal)) =
      ∑ t, ⨅ q ∈ OmegaNR D x t (d t), ((dispCost D q : ℝ) : EReal) := by sorry

end MultistageRUC.Equiv
