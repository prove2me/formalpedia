-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_lemma_3_4
-- name    : ManyServerFluid.Equilibrium.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:58.343865+00:00
-- url     : https://prove2.me/theorems/3cc8ef6a-f57e-4a76-8adb-656476a50bc3
-- title:
--   Lemma 3.4 — a fluid solution restarted at time t is a fluid solution for the shifted data (Ē^[t], X̄(t), ν̄_t)
-- statement:
--   Let $(\bar X,\bar\nu)$ solve the fluid equations associated with $(\bar E,\bar X(0),\bar\nu_0)\in\mathcal S_0$, and let $\bar K$ be the entry process (3.8). For $t\ge0$ put
--   $$\bar E^{[t]}=\bar E(t+\cdot)-\bar E(t),\quad \bar K^{[t]}=\bar K(t+\cdot)-\bar K(t),\quad \bar X^{[t]}=\bar X(t+\cdot),\quad \bar\nu^{[t]}=\bar\nu_{t+\cdot}.$$
--   Then $(\bar E^{[t]},\bar X(t),\bar\nu_t)\in\mathcal S_0$, the pair $(\bar X^{[t]},\bar\nu^{[t]})$ solves the fluid equations associated with this initial condition, and $\bar K^{[t]}$ is its entry process: for every $u\ge0$,
--   $$\langle\mathbf 1,\bar\nu_{t+u}\rangle-\langle\mathbf 1,\bar\nu_t\rangle+\int_0^u\langle h,\bar\nu_{t+r}\rangle\,dr=\bar K(t+u)-\bar K(t).$$
--
--   This is the non-anticipative (time-shift) property of the fluid equations. It lets a solution be restarted from any time, which the proofs of Proposition 6.1(2) and Theorem 3.9(2) use.
--
--   **Formalization Note** The paper omits the proof ("straightforward algebraic manipulations"). Shifted paths are `fun u => X (t + u)` and `fun u => ν (t + u)`; their values at negative $u$ are never read by the fluid equations.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 45, Lemma 3.4

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Lemma 3.4 (p. 45): time-shifting a fluid solution gives a fluid solution for the shifted data. -/
theorem lemma_3_4 (S : ServiceLaw) (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ)
    (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ)
    (hS0 : S.InS0 E X0 ν0) (hsol : S.IsFluidSolution E X0 ν0 X ν) (t : ℝ) (ht : 0 ≤ t) :
    S.InS0 (fun u => E (t + u) - E t) (X t) (ν t) ∧
    S.IsFluidSolution (fun u => E (t + u) - E t) (X t) (ν t)
      (fun u => X (t + u)) (fun u => ν (t + u)) ∧
    ∀ u, 0 ≤ u → S.Kbar (fun u => ν (t + u)) u = S.Kbar ν (t + u) - S.Kbar ν t := by sorry

end ManyServerFluid.Equilibrium
