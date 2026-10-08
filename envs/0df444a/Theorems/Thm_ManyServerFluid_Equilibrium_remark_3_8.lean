-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_remark_3_8
-- name    : ManyServerFluid.Equilibrium.remark_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:11.613989+00:00
-- url     : https://prove2.me/theorems/5aff9412-d6bb-48a9-bcf8-4a3f5b71e9b5
-- title:
--   Remark 3.8 — with λ̄ ≥ 1 a.e., X̄(0) = c ≥ 1 and ν̄_0 = ν̄*, (c + Ē − id, ν̄*) solves the fluid equations with K̄ = id
-- statement:
--   Let $\bar\nu_*$ be the measure on $[0,M)$ with density $1-G$. Suppose the arrival process is absolutely continuous, $\bar E(t)=\int_0^t\bar\lambda(s)\,ds$ for $t\ge0$, with a locally integrable rate satisfying $\bar\lambda\ge1$ almost everywhere on $[0,\infty)$, and let $c\ge1$. Then $(\bar E,c,\bar\nu_*)\in\mathcal S_0$, the pair
--   $$\bar X(t)=c+\bar E(t)-t,\qquad\bar\nu_t=\bar\nu_*,\qquad t\ge0,$$
--   solves the fluid equations associated with $(\bar E,c,\bar\nu_*)$, and its entry process is $\bar K(t)=t$ for every $t\ge0$.
--
--   In particular, for $\bar E=\mathrm{id}$ the constant pair $(c,\bar\nu_*)$ is an invariant solution: a system started full, with ages distributed according to the equilibrium measure, stays there. Theorem 3.9(2) shows that this equilibrium attracts every solution.
--
--   **Formalization Note** The paper verifies (3.6), (3.11) and (3.12) and concludes through the characterization of Theorem 3.5; the statement here is that conclusion, membership in the solution set of Definition 3.3. $\bar\nu_*$ enters as a `FiniteMeasure` whose underlying measure equals the density measure (finite by (2.2)).
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 46, Remark 3.8

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Remark 3.8 (p. 46): with Ē absolutely continuous, derivative λ̄ ≥ 1 a.e., X̄(0) = c ≥ 1 and
ν̄_0 = ν̄*, the pair (c + Ē − id, ν̄*) solves the fluid equations, with K̄ = id. -/
theorem remark_3_8 (S : ServiceLaw) (lam E : ℝ → ℝ) (c : ℝ) (νstar : FiniteMeasure ℝ)
    (hνstar : (νstar : Measure ℝ) = S.nuStar)
    (hlam_int : ∀ t, IntegrableOn lam (Icc 0 t))
    (hE : ∀ t, 0 ≤ t → E t = ∫ s in Icc 0 t, lam s)
    (hlam : ∀ᵐ s ∂(volume.restrict (Ici (0 : ℝ))), 1 ≤ lam s)
    (hc : 1 ≤ c) :
    S.InS0 E c νstar ∧
    S.IsFluidSolution E c νstar (fun t => c + E t - t) (fun _ => νstar) ∧
    ∀ t, 0 ≤ t → S.Kbar (fun _ => νstar) t = t := by sorry

end ManyServerFluid.Equilibrium
