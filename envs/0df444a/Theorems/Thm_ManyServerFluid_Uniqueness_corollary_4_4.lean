-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_corollary_4_4
-- name    : ManyServerFluid.Uniqueness.corollary_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:58.871983+00:00
-- url     : https://prove2.me/theorems/7a97a07f-3433-444b-b1f6-0bb92d32abaa
-- title:
--   Corollary 4.4, (4.5) — K̄ satisfies a renewal equation
-- statement:
--   Let $(\bar X, \bar\nu)$ solve the fluid equations associated with $(\bar E, \bar X(0), \bar\nu_0) \in \mathcal S_0$ and let $\bar K$ be given by (3.8). Then for every $t \ge 0$
--   $$\bar K(t) = \langle\mathbf 1,\bar\nu_t\rangle - \langle\mathbf 1,\bar\nu_0\rangle + \int_{[0,M)}\frac{G(x+t)-G(x)}{1-G(x)}\,\bar\nu_0(dx) + \int_0^t g(t-s)\,\bar K(s)\,ds. \qquad (4.5)$$
--
--   The cumulative entry into service is thus the solution of a renewal equation driven by the change in the number in service and by the departures of the initial customers; this is how $\bar K$ is controlled in the continuity estimate of Theorem 4.6 and in the long-time analysis of the fluid limit.
--
--   **Formalization Note.** Only the renewal equation (4.5) is stated; the representation (4.6) through the renewal measure is not part of this item.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 52, Corollary 4.4, (4.5)

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ManyServerFluid.Uniqueness

/-- Corollary 4.4, (4.5), p. 52: K̄ of a fluid solution satisfies the renewal equation
K̄(t) = ⟨1, ν̄_t⟩ − ⟨1, ν̄_0⟩ + ∫_[0,M) (G(x + t) − G(x))/(1 − G(x)) ν̄_0(dx) + ∫_0^t g(t − s) K̄(s) ds. -/
theorem corollary_4_4 (S : ServiceLaw) (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ)
    (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ) (h0 : S.InS0 E X0 ν0)
    (hsol : S.IsFluidSolution E X0 ν0 X ν) :
    ∀ t, 0 ≤ t →
      S.Kbar ν t = ((ν t).mass : ℝ) - (ν0.mass : ℝ)
        + ∫ x, (S.G (x + t) - S.G x) / (1 - S.G x) ∂(ν0 : Measure ℝ)
        + ∫ s in Icc 0 t, S.g (t - s) * S.Kbar ν s := by sorry

end ManyServerFluid.Uniqueness
