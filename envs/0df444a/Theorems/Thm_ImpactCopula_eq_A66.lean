-- Prove2me | Theorems.Thm_ImpactCopula_eq_A66
-- name    : ImpactCopula.eq_A66
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:56:02.343896+00:00
-- url     : https://prove2.me/theorems/ea492d5a-32b0-4616-aca5-f2b98f09625f
-- title:
--   Eq. (A.66) — on the gaps of $\overline{\mathcal R}_X$, $D_1C(u,v)$ is the slope across the gap, off a null set
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ with marginal distribution functions $F_X$, $F_\theta$, and let $C$ be a copula of $\mu$ that is linearly interpolating on $\overline{\mathcal R}_X^c \times \overline{\mathcal R}_\theta$ with respect to $u$. Then there is a Lebesgue-null set $E_1 \subseteq \mathbb R$ such that, for every discontinuity point $d \in \Delta_X$ of $F_X$, every $u \in (F_X(d-), F_X(d)) \setminus E_1$ and every $v \in \overline{\mathcal R}_\theta$,
--
--   $$
--   D_1C(u, v) = \frac{C(F_X(d), v) - C(F_X(d-), v)}{F_X(d) - F_X(d-)} . \tag{A.66}
--   $$
--
--   This is the first step of the proof of the "if" part of Theorem 2: on the gaps of the range of $F_X$, the conditional distribution function $D_1C(u,\cdot)$ does not depend on $u$ (on $\overline{\mathcal R}_\theta$).
--
--   Differences from the source:
--   - encoding: $\Delta_X$, $F_X(d-)$, "Lebesgue measure 0" → points where `cdfX μ` is not continuous, `Function.leftLim (cdfX μ) d`, `volume E₁ = 0`; reason: Lean convention; same objects.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, step one, eq. (A.66), p.79 (PDF p.82)

import Mathlib
import Definitions.Def_ImpactCopula_IsCopulaOf
import Definitions.Def_ImpactCopula_IsLinearlyInterpolating
import Definitions.Def_ImpactCopula_mpdd

open MeasureTheory

namespace ImpactCopula

/-- **(A.66) on the gaps of `R̄_X`**, proof of Theorem 2, step one, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.79 (PDF p.82):
if the copula `C` of `F` is linearly interpolating, there is a Lebesgue-null set `E₁` such that
"(A.66) holds for any d ∈ Δ_X, u ∈ (F_X(d−), F_X(d)) \ E₁ and v ∈ R̄_θ", where (A.66) is
`D₁C(u, v) = (C(F_X(d), v) − C(F_X(d−), v))/(F_X(d) − F_X(d−))`.

**Formalization Note.** `Δ_X` is the set of discontinuity points of `F_X`, `F_X(d−)` is
`Function.leftLim (cdfX μ) d`, `R̄_θ` is `rbarTheta μ`, "Lebesgue measure 0" is `volume E₁ = 0`. -/
theorem eq_A66 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C : ℝ → ℝ → ℝ)
    (hC : IsCopulaOf C μ) (hLI : IsLinearlyInterpolating C μ) :
    ∃ E₁ : Set ℝ, volume E₁ = 0 ∧
      ∀ d : ℝ, ¬ ContinuousAt (cdfX μ) d →
        ∀ u ∈ Set.Ioo (Function.leftLim (cdfX μ) d) (cdfX μ d), u ∉ E₁ →
          ∀ v ∈ rbarTheta μ,
            mpdd C u v = (C (cdfX μ d) v - C (Function.leftLim (cdfX μ) d) v) /
              (cdfX μ d - Function.leftLim (cdfX μ) d) := by sorry

end ImpactCopula
