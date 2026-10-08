-- Prove2me | Theorems.Thm_KingmanSubadditive_BanachAlgebra_positive_part_finite
-- name    : KingmanSubadditive.BanachAlgebra.positive_part_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:17.28401+00:00
-- url     : https://prove2.me/theorems/3cf6a749-1f2a-471e-8ff8-10727945652d
-- title:
--   (1.2.7), p. 885 — under S₁, S₂ and S₃′, E(x_st⁺) < ∞ for all s < t
-- statement:
--   Let $x=(x_{st})_{s<t}$ be a family of real random variables indexed by nonnegative integers $s<t$ that satisfies condition S₁ ($x_{su}\le x_{st}+x_{tu}$ whenever $s<t<u$), condition S₂ (the joint distributions of $(x_{s+1,t+1})$ are those of $(x_{st})$) and condition S₃′, $E(x_{01}^+)<\infty$. Then
--   $$E(x_{st}^+)<\infty\qquad\text{for all } s<t .$$
--
--   This is the remark (1.2.7) of §1.2: the weakened moment condition S₃′ on the single variable $x_{01}$ propagates to every variable of the process. It is what makes the truncated processes of the proof of Theorem 2 integrable.
--
--   **Formalization Note** $x^+=\max(x,0)$ and the expectation of $x^+$ is a lower Lebesgue integral in $[0,\infty]$. S₁ is assumed almost surely for each triple.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 885, §1.2, (1.2.7)

import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- **(1.2.7), §1.2, p. 885** (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899
(1973), DOI 10.1214/aop/1176996798). "Note that by (1.1.1) this implies that `E(x_st⁺) < ∞` for
all `s < t`": if a measurable family of real random variables satisfies S₁, S₂ and S₃′
(`E(x₀₁⁺) < ∞`), then `E(x_st⁺) < ∞` for every `s < t`.

**Formalization Note.** The positive part `x⁺ = max(x, 0)` is integrated as a lower Lebesgue
integral of `ENNReal.ofReal`. S₂ (joint-law stationarity) is among the hypotheses because it is
what transports `E(x₀₁⁺) < ∞` to `E(x_{r,r+1}⁺) < ∞`; S₃ is not assumed. -/
theorem positive_part_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x) :
    ∀ s t : ℕ, s < t → ∫⁻ ω, ENNReal.ofReal (x s t ω) ∂P < ⊤ := by sorry

end KingmanSubadditive.BanachAlgebra
