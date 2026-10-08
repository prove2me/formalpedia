-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_proposition_6_1_3
-- name    : ManyServerFluid.Equilibrium.proposition_6_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:32.741282+00:00
-- url     : https://prove2.me/theorems/a149efc6-6766-46de-a130-be7cac220a46
-- title:
--   Proposition 6.1(3) — comparison with the empty start: ⟨1, ν̄⋄_t⟩ ≥ ⟨1, ν̄_t⟩ on [0, τ_1), (6.2), and (6.3)
-- statement:
--   Suppose Assumption 2 holds, $\bar E(t)=\int_0^t\bar\lambda(s)\,ds$ for $t\ge0$ with $\bar\lambda$ locally integrable, $(\bar E,0,\tilde{\mathbf 0})\in\mathcal S_0$, and $(\bar X,\bar\nu)$ solves the associated fluid equations. Let $(\bar X^\diamond,\bar\nu^\diamond)$ solve the fluid equations associated with any other initial condition $(\bar E,\bar X^\diamond(0),\bar\nu^\diamond_0)\in\mathcal S_0$ with the same arrival process. With $\tau_1$ as in (6.1):
--
--   1. for every $t\in[0,\tau_1)$,
--   $$\langle\mathbf 1,\bar\nu^\diamond_t\rangle\ge\langle\mathbf 1,\bar\nu_t\rangle;\qquad(6.2)$$
--   2. if moreover $\bar\lambda$ is a constant $\bar\lambda\in[0,1]$, then for every $t\in[0,\tau_1)$,
--   $$\langle\mathbf 1,\bar\nu^\diamond_t\rangle\ge\bar\lambda\int_0^t(1-G(r))\,dr.\qquad(6.3)$$
--
--   Starting with customers already present can only increase the number in service before the empty system first fills up. The proof of Theorem 3.9(2) uses this to show that the occupancy of an arbitrary solution with $\bar E=\mathrm{id}$ tends to $1$.
--
--   **Formalization Note** "$\bar\lambda(\cdot)$ is a constant" is stated as $\bar\lambda=c$ almost everywhere on $[0,\infty)$: $\bar\lambda$ enters only through $\bar E$ and $\tau_1$, both of which are integrals, so this is the same hypothesis. Assumption 2 is the standing hypothesis of Section 6.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 105, Proposition 6.1(3), (6.2), (6.3)

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Proposition 6.1(3) (p. 105): any solution with the same arrivals has at least as many
customers in service as the empty-start solution on [0, τ_1), (6.2); with constant rate λ̄, (6.3). -/
theorem proposition_6_1_3 (S : ServiceLaw) (hA2 : S.Assumption2)
    (lam E X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ)
    (hlam_int : ∀ t, IntegrableOn lam (Icc 0 t))
    (hE : ∀ t, 0 ≤ t → E t = ∫ s in Icc 0 t, lam s)
    (hS0 : S.InS0 E 0 0) (hsol : S.IsFluidSolution E 0 0 X ν)
    (Xd0 : ℝ) (νd0 : FiniteMeasure ℝ) (Xd : ℝ → ℝ) (νd : ℝ → FiniteMeasure ℝ)
    (hS0d : S.InS0 E Xd0 νd0) (hsold : S.IsFluidSolution E Xd0 νd0 Xd νd) :
    (∀ t : ℝ, 0 ≤ t → (t : EReal) < S.tau1 lam → ((ν t).mass : ℝ) ≤ ((νd t).mass : ℝ)) ∧
    ∀ c : ℝ, 0 ≤ c → c ≤ 1 → (∀ᵐ s ∂(volume.restrict (Ici (0 : ℝ))), lam s = c) →
      ∀ t : ℝ, 0 ≤ t → (t : EReal) < S.tau1 lam →
        c * ∫ r in Icc 0 t, (1 - S.G r) ≤ ((νd t).mass : ℝ) := by sorry

end ManyServerFluid.Equilibrium
