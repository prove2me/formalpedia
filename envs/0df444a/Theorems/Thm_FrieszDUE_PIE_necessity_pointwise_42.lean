-- Prove2me | Theorems.Thm_FrieszDUE_PIE_necessity_pointwise_42
-- name    : FrieszDUE.PIE.necessity_pointwise_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:19:14.485257+00:00
-- url     : https://prove2.me/theorems/65e6eb87-4257-4ce9-b882-cb716a7582be
-- title:
--   (42), proof of Theorem 2 part i, p. 187 — at an SRD equilibrium {C_p(t, h*) − μ*_kl}[h_p(t) − h*_p(t)] ≥ 0 for ν-a.a. t
-- statement:
--   In the setting of the PIE model (horizon $T$, paths $P$, OD pairs, demands $Q$, cost operator $C$, Lebesgue measure $\nu$ on $[0,T]$, feasible set $\Lambda$ of (38)), let $(h^*,\mu^*)$ be a simultaneous route-departure equilibrium (Definition 3) and let $h\in\Lambda$. Then for every OD pair $kl$ and every path $p\in P_{kl}$,
--
--   $$\{C_p(t,h^*)-\mu^*_{kl}\}\,[h_p(t)-h^*_p(t)]\ge 0\qquad\forall_\nu(t).$$
--
--   This pointwise inequality is the core of the necessity half of Theorem 2: integrated over $[0,T]$ and summed over paths it yields the variational inequality (39).
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 187, proof of Theorem 2 part i, (42)–(43)

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Proof of Theorem 2 part i, (42), p. 187. -/
theorem necessity_pointwise_42 {P W : Type*} [Fintype P] [DecidableEq W]
    (T : ℝ) (od : P → W) (Q : W → ℝ) (C : P → ℝ → (P → ℝ → ℝ) → ℝ)
    (hs : P → ℝ → ℝ) (mu : W → ℝ) (heq : IsSRDEquilibrium T od Q C hs mu)
    (h : P → ℝ → ℝ) (hh : h ∈ Lambda T od Q) :
    ∀ p, ∀ᵐ t ∂(ν T), 0 ≤ (C p t hs - mu (od p)) * (h p t - hs p t) := by sorry

end FrieszDUE.PIE
