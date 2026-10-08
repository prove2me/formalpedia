-- Prove2me | Theorems.Thm_KingmanSubadditive_StationaryIncrements_theorem_3
-- name    : KingmanSubadditive.StationaryIncrements.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:42:40.535866+00:00
-- url     : https://prove2.me/theorems/817aab2c-ba5e-40fe-914b-d790b052d1dc
-- title:
--   Theorem 3 — for every positive increasing Γ there is a $C^\infty$ process with stationary increments, finite expectations, and $P\{|y_t|\le\Gamma(t)$ for all large $t\}=0$
-- statement:
--   Let $\Gamma(t)$, $t>0$, be any positive non-decreasing function. Then there exist a probability space $(\Omega,\mathcal F,P)$ and a real process $(y_t;\,t\ge0)$ on it such that
--
--   1. $(y_t)$ has stationary increments: for every $\tau\ge0$, $(y_{t+\tau}-y_\tau)_{t\ge0}$ has the same joint law as $(y_t-y_0)_{t\ge0}$;
--   2. $(y_t)$ has finite expectations: $E|y_t|<\infty$ for every $t\ge0$;
--   3. every sample function $t\mapsto y_t(\omega)$ has derivatives of all orders on $[0,\infty)$;
--   4. (1.4.4) holds:
--   $$ P\{|y_t|\le\Gamma(t)\ \text{for all sufficiently large } t\}=0 . $$
--
--   If Theorem 1 extended to continuous-parameter subadditive processes under separability alone, every separable process with stationary increments and finite expectations would have $\lim_{t\to\infty}y_t/t$ finite with probability one. Theorem 3 shows that this fails in a strong sense: even a smooth such process can outgrow any prescribed function along a sequence of times, almost surely. This is why Kingman's Theorem 4 needs an extra integrability condition on the oscillation.
--
--   **Formalization Note** The quantifier order is "for every $\Gamma$ there exist $(\Omega,P,y)$". "Increasing" is read as non-decreasing on $(0,\infty)$, the weaker hypothesis. $\Gamma$ is a total function on $\mathbb R$ whose values at $t\le0$ are irrelevant. The process is $y:\mathbb R\to\Omega\to\mathbb R$, used for $t\ge0$, with every $y_t$ measurable. Smoothness is the order `((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. $C^\infty$, not analytic. The time in (1.4.4) is real (`∀ᶠ t in atTop` on `ℝ`). The event need not be measurable a priori, and $P$ of it is its outer measure.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 888, §1.4, Theorem 3, (1.4.4)

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
open MeasureTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Theorem 3** (p. 888, §1.4) — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"Let `Γ(t)` (`t > 0`) be any positive increasing function. Then there exists a process
`(y_t; t ≥ 0)` with stationary increments and finite expectations, whose sample functions have
derivatives of all orders, such that
(1.4.4) `P{|y_t| ≤ Γ(t) for all sufficiently large t} = 0`."

**Formalization Note.** The quantifier order is `∀ Γ, ∃ (Ω, P, y)`. "Increasing" is read as
non-decreasing (`MonotoneOn Γ (Set.Ioi 0)`, the weaker hypothesis); `Γ` is a total function on
`ℝ` whose values at `t ≤ 0` are irrelevant. The process is `y : ℝ → Ω → ℝ`, used for `t ≥ 0`;
each `y_t` is measurable. Stationary increments: `HasStationaryIncrements` (joint laws of the
increment processes on `[0, ∞)`, product σ-algebra). Finite expectations: each `y_t`
(`t ≥ 0`) is integrable. Derivatives of all orders: every sample path is `C^∞` on `[0, ∞)`
(order `((⊤ : ℕ∞) : WithTop ℕ∞)`, smooth; not analytic). In (1.4.4), "for all sufficiently large
`t`" ranges over **real** `t` (`∀ᶠ t in atTop` on `ℝ`); the event need not be measurable a
priori, and `P` of it is its outer measure. -/
theorem theorem_3 (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ y : ℝ → Ω → ℝ,
        (∀ t : ℝ, 0 ≤ t → Measurable (y t)) ∧
        HasStationaryIncrements P y ∧
        (∀ t : ℝ, 0 ≤ t → Integrable (y t) P) ∧
        (∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => y t ω) (Set.Ici 0)) ∧
        P {ω | ∀ᶠ t in atTop, |y t ω| ≤ Γ t} = 0 := by sorry

end KingmanSubadditive.StationaryIncrements
