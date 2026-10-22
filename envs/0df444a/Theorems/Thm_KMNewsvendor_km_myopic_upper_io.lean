-- Prove2me | Theorems.Thm_KMNewsvendor_km_myopic_upper_io
-- name    : KMNewsvendor.km_myopic_upper_io
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T03:51:28.78688+00:00
-- url     : https://prove2.me/theorems/bcc1917b-704a-41d1-a8b8-4d902920b168
-- title:
--   Lemma 3 — with a flat optimum the policy reaches the upper quantile $\tilde\psi^*$ infinitely often
-- statement:
--   Let the demands $D_1,D_2,\dots$ be independent copies of a nonnegative integer-valued random variable $D$ with $P[D=0]=0$, let $h,b>0$, $r^*=b/(b+h)$, and let $\psi^*$ and $\tilde\psi^*$ be the newsvendor quantile and the upper quantile. Assume the optimum is not unique:
--   $$\bar F(\psi^*)=1-r^* .$$
--   Then the KM-myopic policy with target ratio $r^*$ and initial order $y_1\ge1$ satisfies
--   $$P\big[Y^{KM}_t\ge\tilde\psi^*\ \text{i.o.}\big]=1 .$$
--   Consequently $\mathcal R=\tilde\psi^*$ in this case, and by Lemma 2 (i) the estimators converge at $\tilde\psi^*$, which is what keeps the orders from eventually exceeding $\tilde\psi^*$.
--
--   **Formalization Note** "$P[\cdot\ \text{i.o.}]=1$" is "almost surely, frequently in $T$". The hypotheses $P[D=0]=0$ and $y_1\ge1$ are added to the printed statement, which is false without them (the policy can be absorbed at $0$, and $\tilde\psi^*\ge\psi^*\ge1$ here because $\bar F(\psi^*)=1-r^*<1$ forces $\psi^*\ge1$ once $P[D=0]=0$). Time is $0$-based in Lean.
-- source:
--   Huh, Levi, Rusmevichientong, Orlin, Adaptive Data-Driven Inventory Control with Censored Demand Based on Kaplan-Meier Estimator, Oper. Res. 59(4) (2011), doi:10.1287/opre.1100.0906, p. 936, Lemma 3 (with added hypotheses P[D = 0] = 0 and y_1 >= 1)

import Mathlib
import Definitions.Def_KMNewsvendor_quantile
import Definitions.Def_KMNewsvendor_kmSurv
import Definitions.Def_KMNewsvendor_kmOrder
import Definitions.Def_KMNewsvendor_radius
open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace KMNewsvendor

/-- Lemma 3 (p. 936), with the added hypotheses `P[D = 0] = 0` and `1 ≤ y₁`: if
`F̄(ψ*) = 1 - r*` (the optimum is not unique), then almost surely the KM-myopic policy orders
at least the upper quantile `ψ̃*` in infinitely many periods. -/
theorem km_myopic_upper_io {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℕ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (y₁ : ℕ)
    (hD0 : μ {ω | D 0 ω = 0} = 0) (hy₁ : 1 ≤ y₁)
    (hflat : survival μ (D 0) (quantile μ (D 0) (critRatio b h)) = 1 - critRatio b h) :
    ∀ᵐ ω ∂μ, ∃ᶠ T in atTop,
      upperQuantile μ (D 0) (critRatio b h) ≤
        kmOrder (critRatio b h) y₁ (fun t => D t ω) T := by sorry

end KMNewsvendor
