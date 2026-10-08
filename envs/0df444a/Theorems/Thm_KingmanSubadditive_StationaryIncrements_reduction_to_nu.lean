-- Prove2me | Theorems.Thm_KingmanSubadditive_StationaryIncrements_reduction_to_nu
-- name    : KingmanSubadditive.StationaryIncrements.reduction_to_nu
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:43:25.380139+00:00
-- url     : https://prove2.me/theorems/4458465f-27c9-4bb7-9ed3-55d7f3945790
-- title:
--   Proof of Theorem 3, p. 889 — $P\{|y_t|\le\Gamma(t)$ eventually$\}\le P\{\nu_n\le\Gamma(n+\frac12)$ eventually$\}=0$
-- statement:
--   In the construction of the proof of Theorem 3 ($\Gamma$ positive and non-decreasing on $(0,\infty)$, $\psi$ the bump function, $\eta,\nu_0,\nu_1,\dots$ independent with $\eta$ uniform on $(0,1)$ and every $\nu_r$ with law $m_\Gamma$, $y_t=Y_{t+\eta}$ as in (1.4.5)), put $t_n=n+\tfrac12\nu_n^{-1}-\eta$. Then
--   $$
--   \begin{aligned}
--   P\{|y_t|\le\Gamma(t)\text{ for all sufficiently large }t\}
--   &\le P\{|y(t_n)|\le\Gamma(t_n)\text{ for all sufficiently large }n\}\\
--   &\le P\{\nu_n\le\Gamma(n+\tfrac12)\text{ for all sufficiently large }n\}\\
--   &=0 .
--   \end{aligned}
--   $$
--
--   The times $t_n$ are the points where $y$ reaches its peak $\nu_n$ in the $n$-th unit interval. The chain reduces the event about the continuous-time path to an event about the independent sequence $(\nu_n)$, to which the second Borel–Cantelli lemma applies.
--
--   **Formalization Note** "For all sufficiently large $t$" ranges over real $t$ (`∀ᶠ t in atTop` on `ℝ`), and "for all sufficiently large $n$" over natural numbers. These events need not be measurable a priori, and $P$ of a set is its outer measure. $\nu_n^{-1}$ is the real inverse; $\nu_n\ge1$ almost surely.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 889, §1.4, proof of Theorem 3

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Proof of Theorem 3, p. 889 (unnumbered; §1.4)** — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"`P{|y_t| ≤ Γ(t) for all sufficiently large t}
≤ P{|y(n + ½ν_n⁻¹ − η)| ≤ Γ(n + ½ν_n⁻¹ − η) for all sufficiently large n}
≤ P{ν_n ≤ Γ(n + ½) for all sufficiently large n} = 0`."

For the construction of the proof of Theorem 3 (`Γ` positive and increasing on `(0, ∞)`,
`IsBump ψ`, `IsConstruction Γ P η ν`), with `t_n = n + ½ν_n⁻¹ − η`:
1. `P{|y_t| ≤ Γ(t) for all large real t} ≤ P{|y(t_n)| ≤ Γ(t_n) for all large n}`;
2. `P{|y(t_n)| ≤ Γ(t_n) for all large n} ≤ P{ν_n ≤ Γ(n + ½) for all large n}`;
3. `P{ν_n ≤ Γ(n + ½) for all large n} = 0`.

**Formalization Note.** "For all sufficiently large `t`" is `∀ᶠ t in atTop` over the reals,
"for all sufficiently large `n`" is `∀ᶠ n in atTop` over `ℕ`. These events need not be
measurable a priori; `P` of a set is its outer measure. `ν_n⁻¹` is the real inverse (`ν_n ≥ 1`
almost surely). -/
theorem reduction_to_nu {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    P {ω | ∀ᶠ t in atTop, |procY ψ η ν t ω| ≤ Γ t}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop,
            |procY ψ η ν ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω) ω|
              ≤ Γ ((n : ℝ) + 1 / 2 * (ν n ω : ℝ)⁻¹ - η ω)}
        ≤ P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} ∧
      P {ω | ∀ᶠ n : ℕ in atTop, (ν n ω : ℝ) ≤ Γ ((n : ℝ) + 1 / 2)} = 0 := by sorry

end KingmanSubadditive.StationaryIncrements
