-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_corollary_4_4_eq_4_6
-- name    : ManyServerFluid.Equilibrium.corollary_4_4_eq_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:19.228988+00:00
-- url     : https://prove2.me/theorems/1a95a527-0a13-4d6a-b4b8-674b11ef1f26
-- title:
--   Corollary 4.4, (4.6) — K̄ = U ∗ (the forcing term of (4.5))
-- statement:
--   Let $(\bar X,\bar\nu)$ solve the fluid equations associated with $(\bar E,\bar X(0),\bar\nu_0)\in\mathcal S_0$, let $\bar K$ be its entry process (3.8), and let $U=\sum_{n\ge0}G^{*n}$ be the renewal measure of $G$. Then for every $t\ge0$,
--   $$\bar K(t)=\int_{[0,t]}\big(\langle\mathbf 1,\bar\nu_{t-s}\rangle-\langle\mathbf 1,\bar\nu_0\rangle\big)\,dU(s)+\int_{[0,t]}\Big(\int_{[0,M)}\frac{G(x+t-s)-G(x)}{1-G(x)}\,\bar\nu_0(dx)\Big)dU(s).\qquad(4.6)$$
--
--   This is the solution of the renewal equation (4.5) satisfied by $\bar K$: entries into service are expressed through the occupancy $\langle\mathbf 1,\bar\nu\rangle$ and the initial ages. Section 6 uses it, applied after a time shift, to compare a fluid solution with the reference system of Lemma 6.2.
--
--   **Formalization Note** $U$ includes the unit mass at $0$. Both integrals are Bochner integrals against $U$ restricted to $[0,t]$; their integrands are bounded and $U$ is finite on bounded sets. The renewal equation (4.5) itself belongs to the companion mission on uniqueness and is not restated here.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 52, Corollary 4.4, (4.6)

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Corollary 4.4, (4.6) (p. 52): K̄ = U ∗ (the forcing term of the renewal equation (4.5)),
with U the renewal measure of G (δ_0 included). -/
theorem corollary_4_4_eq_4_6 (S : ServiceLaw) (E : ℝ → ℝ) (X0 : ℝ) (ν0 : FiniteMeasure ℝ)
    (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ)
    (hS0 : S.InS0 E X0 ν0) (hsol : S.IsFluidSolution E X0 ν0 X ν) :
    ∀ t, 0 ≤ t → S.Kbar ν t =
      ∫ s in Icc 0 t, (((ν (t - s)).mass : ℝ) - (ν0.mass : ℝ)) ∂S.renewalMeasure
      + ∫ s in Icc 0 t,
          (∫ x, (S.G (x + t - s) - S.G x) / (1 - S.G x) ∂(ν0 : Measure ℝ))
            ∂S.renewalMeasure := by sorry

end ManyServerFluid.Equilibrium
