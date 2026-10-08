-- Prove2me | Theorems.Thm_KingmanSubadditive_StationaryIncrements_stationary_smooth
-- name    : KingmanSubadditive.StationaryIncrements.stationary_smooth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:42:42.40514+00:00
-- url     : https://prove2.me/theorems/2a45e23e-9e9f-4021-831e-bb880f3cb01f
-- title:
--   Proof of Theorem 3, p. 888 — $(y_t)$ is stationary, has stationary increments, and has $C^\infty$ sample functions
-- statement:
--   Let $\Gamma$ be positive and non-decreasing on $(0,\infty)$, let $\psi$ be the bump function of the construction, and let $\eta,\nu_0,\nu_1,\dots$ be independent random variables with $\eta$ uniform on $(0,1)$ and every $\nu_r$ with law $m_\Gamma$. Let
--   $$ y_t=Y_{t+\eta},\qquad Y_s=\nu_n\,\psi[\nu_n(s-n)]\quad(n\le s<n+1), $$
--   be the process (1.4.5). Then
--
--   1. $(y_t)_{t\ge0}$ is stationary: for every $\tau\ge0$, $(y_{t+\tau})_{t\ge0}$ and $(y_t)_{t\ge0}$ have the same joint law;
--   2. $(y_t)_{t\ge0}$ has stationary increments;
--   3. for every sample point $\omega$, the sample function $t\mapsto y_t(\omega)$ is of class $C^\infty$ on $[0,\infty)$.
--
--   This is the step of the proof of Theorem 3 that gives the constructed process two of the three properties the theorem requires.
--
--   **Formalization Note** Smoothness is the order `((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. $C^\infty$ and not analytic, and it is claimed for every $\omega$, not only almost every one.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 888, §1.4, proof of Theorem 3 (after (1.4.5))

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Proof of Theorem 3, p. 888 (unnumbered; §1.4)** — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"Then `(y_t)` is clearly stationary, and therefore has stationary increments, and its sample
functions are of class `C^∞`."

Let `Γ` be positive and increasing on `(0, ∞)`, `ψ` the bump function of the proof (`IsBump`),
and `η, ν₀, ν₁, …` independent, `η` uniform on `(0, 1)`, each `ν_r` with law `m_Γ`
(`IsConstruction`). Then the process `y_t = Y_{t+η}` of (1.4.5) is stationary, has stationary
increments, and every sample path `t ↦ y_t(ω)` is `C^∞` on `[0, ∞)`.

**Formalization Note.** `C^∞` is the order `((⊤ : ℕ∞) : WithTop ℕ∞)` (smooth), not
`⊤ : WithTop ℕ∞` (analytic). Smoothness is claimed for every `ω`, not almost every. -/
theorem stationary_smooth {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    IsStationary P (procY ψ η ν) ∧ HasStationaryIncrements P (procY ψ η ν) ∧
      ∀ ω : Ω, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => procY ψ η ν t ω) (Set.Ici 0) := by sorry

end KingmanSubadditive.StationaryIncrements
