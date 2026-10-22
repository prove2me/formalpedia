-- Prove2me | Theorems.Thm_KMNewsvendor_km_myopic_eventually_optimal
-- name    : KMNewsvendor.km_myopic_eventually_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T04:02:01.893016+00:00
-- url     : https://prove2.me/theorems/fa36b3bb-4679-425e-8830-40e92993f29d
-- title:
--   Theorem 1 — KM-myopic orders eventually lie in the newsvendor optimal set $\{\psi^*,\tilde\psi^*\}$
-- statement:
--   Consider the repeated newsvendor problem with per-unit overage cost $h>0$, per-unit lost-sales penalty $b>0$ and critical ratio $r^*=b/(b+h)$. The demands $D_1,D_2,\dots$ are independent copies of a nonnegative integer-valued random variable $D$ with $P[D=0]=0$, whose distribution is unknown; in each period only the sales $\min\{D_t,Y_t\}$ and whether demand was met are observed. Let $\psi^*$ be the newsvendor quantile and $\tilde\psi^*$ the upper quantile of $D$ at $r^*$. Run the KM-myopic policy (Kaplan–Meier estimate from past censored sales, then order its empirical $r^*$-quantile, or twice the largest observation when that quantile does not exist) from an initial order $y_1\ge1$. Then for almost every demand path $\omega$ there is $T_\omega$ such that
--   $$Y^{KM}_T(\omega)\in\{\psi^*,\tilde\psi^*\}\qquad\text{for all }T\ge T_\omega .$$
--   In particular $\psi^*\le\liminf_T Y^{KM}_T\le\limsup_T Y^{KM}_T\le\tilde\psi^*$ almost surely.
--
--   This is the main result of the paper: a purely data-driven policy that sees only censored sales eventually orders an optimal newsvendor quantity on almost every sample path, with no parametric assumption on the demand.
--
--   **Formalization Note** The hypotheses $P[D=0]=0$ and $y_1\ge1$ are added to the printed theorem, which is false without them. With $P[D=0]>0$ the event $D_1=0$ has positive probability; on it the first observation is an uncensored $0$, every later order is $0$ (both the empirical quantile and the fallback $2Z_{(T)}$ are $0$), and the conclusion fails whenever $\psi^*\ge1$. With $y_1=0$ the same absorption happens on every path. The initial order is not specified in the source and is an explicit parameter. Lean's period $n$ is the source's period $n+1$; the conclusion is the source's "That is" form (eventual membership), which implies its displayed $\liminf/\limsup$ form.
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 937, Theorem 1 ('That is' form; with added hypotheses P[D = 0] = 0 and y_1 >= 1)

import Mathlib
import Definitions.Def_KMNewsvendor_quantile
import Definitions.Def_KMNewsvendor_kmSurv
import Definitions.Def_KMNewsvendor_kmOrder
import Definitions.Def_KMNewsvendor_radius
open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace KMNewsvendor

/-- Theorem 1 (p. 937), "That is" form, with the added hypotheses `P[D = 0] = 0` and `1 ≤ y₁`
(as printed the theorem is false: with `P[D = 0] > 0` the policy is absorbed at `0` with
positive probability). Almost surely the KM-myopic orders eventually lie in `{ψ*, ψ̃*}`. -/
theorem km_myopic_eventually_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℕ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (y₁ : ℕ)
    (hD0 : μ {ω | D 0 ω = 0} = 0) (hy₁ : 1 ≤ y₁) :
    ∀ᵐ ω ∂μ, ∀ᶠ T in atTop,
      kmOrder (critRatio b h) y₁ (fun t => D t ω) T = quantile μ (D 0) (critRatio b h) ∨
      kmOrder (critRatio b h) y₁ (fun t => D t ω) T =
        upperQuantile μ (D 0) (critRatio b h) := by sorry

end KMNewsvendor
