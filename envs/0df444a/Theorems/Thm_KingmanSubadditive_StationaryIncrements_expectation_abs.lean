-- Prove2me | Theorems.Thm_KingmanSubadditive_StationaryIncrements_expectation_abs
-- name    : KingmanSubadditive.StationaryIncrements.expectation_abs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:43:00.26599+00:00
-- url     : https://prove2.me/theorems/78bde3ee-84a6-42f9-931f-cd9a8101988c
-- title:
--   Proof of Theorem 3, p. 888 — $E(|y_t|)=E(y_0)=\int_0^1\psi(u)\,du<\infty$
-- statement:
--   In the construction of the proof of Theorem 3 ($\Gamma$ positive and non-decreasing on $(0,\infty)$, $\psi$ the bump function, $\eta,\nu_0,\nu_1,\dots$ independent with $\eta$ uniform on $(0,1)$ and every $\nu_r$ with law $m_\Gamma$, and $y_t=Y_{t+\eta}$ as in (1.4.5)), every $y_t$ with $t\ge0$ is integrable, and
--   $$ E(|y_t|)=E(y_0)=\int_0^1\psi(u)\,du . $$
--
--   The right-hand side does not depend on $\Gamma$. This gives the "finite expectations" part of Theorem 3, even though $E(\nu_0)$ itself may be infinite.
--
--   **Formalization Note** Integrability is part of the conclusion, so the expectations are genuine Bochner integrals, not the value $0$ that Lean assigns to the integral of a non-integrable function.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 888, §1.4, proof of Theorem 3 (display after (1.4.5))

import Mathlib
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Stationarity
import Definitions.Def_KingmanSubadditive_StationaryIncrements_Construction
open MeasureTheory ProbabilityTheory Filter

namespace KingmanSubadditive.StationaryIncrements

/-- **Proof of Theorem 3, p. 888 (unnumbered; §1.4)** — Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798.

"Moreover, `E(|y_t|) = E(y₀) = ∫₀¹ E(Y_s) ds = E ∫₀¹ ν₀ψ(ν₀s) ds = E ∫₀^{ν₀} ψ(u) du
= ∫₀¹ ψ(u) du < ∞`."

For the construction of the proof of Theorem 3 (`IsBump ψ`, `IsConstruction Γ P η ν`), every
`y_t` (`t ≥ 0`) is integrable, and
`E(|y_t|) = E(y_0) = ∫₀¹ ψ(u) du`.

**Formalization Note.** Integrability is stated explicitly, so the Bochner integrals are not the
junk value `0` of a non-integrable function. Finiteness of `∫₀¹ ψ` is automatic in `ℝ`. -/
theorem expectation_abs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Γ : ℝ → ℝ) (hΓpos : ∀ t : ℝ, 0 < t → 0 < Γ t)
    (hΓmono : MonotoneOn Γ (Set.Ioi 0)) (ψ : ℝ → ℝ) (hψ : IsBump ψ) (η : Ω → ℝ)
    (ν : ℕ → Ω → ℕ) (hC : IsConstruction Γ P η ν) :
    ∀ t : ℝ, 0 ≤ t →
      Integrable (procY ψ η ν t) P ∧
        ∫ ω, |procY ψ η ν t ω| ∂P = ∫ ω, procY ψ η ν 0 ω ∂P ∧
        ∫ ω, procY ψ η ν 0 ω ∂P = ∫ u in (0 : ℝ)..1, ψ u := by sorry

end KingmanSubadditive.StationaryIncrements
