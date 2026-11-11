-- Prove2me | Theorems.Thm_MemoSDPI_Main_theorem_3_1
-- name    : MemoSDPI.Main.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:42:58.038486+00:00
-- url     : https://prove2.me/theorems/de77d8fe-4595-4abd-902b-eb4fc65c69ab
-- title:
--   Theorem 3.1 — Gaussian location model: (θ, S) satisfies an nσ²/(1+nσ²)-SDPI and mem_n(A, P) ≥ I(A(S); θ)/(nσ²)
-- statement:
--   Let $\sigma > 0$ and $\theta \sim N(0, \sigma^2 I_d)$, and let $S = (X_1, \dots, X_n)$ with $X_i = \theta + Z_i$, where $Z_1, \dots, Z_n$ are independent $N(0, I_d)$ variables independent of $\theta$; let $P$ be the resulting average-case problem. Then $(\theta, S)$ satisfies an $\eta$-SDPI with
--   $$
--   \eta = \frac{n\sigma^2}{1 + n\sigma^2},
--   $$
--   and every algorithm $A$ satisfies
--   $$
--   \mathrm{mem}_n(A, P) \;\ge\; \frac{I(A(S); \theta)}{n\sigma^2}. \tag{3.1}
--   $$
--   Since $(1-\eta)/\eta = 1/(n\sigma^2)$, (3.1) is Proposition 2.3 for this model.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ`. Given $\theta$, the records are i.i.d. $N(\theta, I_d)$ (the law of $\theta + Z_i$), via the mission's `gaussPrior` and `gaussLocation`. The bound (3.1) is a division in $[0,\infty]$ by `ENNReal.ofReal (n σ²)`. Every output space $Y$ is allowed.
--
--   Differences from the source:
--   - encoding: X_i = θ + Z_i with Z_i independent N(0, I_d) → given θ, records i.i.d. from N(θ, I_d) = ⊗_j N(θ_j, 1); reason: same joint law of (θ, S)
--   - encoding: mem_n(A, P) ≥ I(A(S); θ)/(nσ²) → I / ENNReal.ofReal (n σ²) ≤ memAvg in ℝ≥0∞; reason: informations take values in [0, ∞]
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 11, Theorem 3.1

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_SDPI
import Definitions.Def_MemoSDPI_Main_Memorization
import Definitions.Def_MemoSDPI_Main_GaussianModel

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 11, Theorem 3.1: for `θ ∼ N(0, σ² I_d)` and `X_i = θ + Z_i` with independent
`Z_i ∼ N(0, I_d)`, the pair `(θ, S)` satisfies an `η`-SDPI with `η = nσ²/(1 + nσ²)`, and every
algorithm satisfies `mem_n(A, P) ≥ I(A(S); θ)/(nσ²)` (eq. (3.1)). -/
theorem theorem_3_1 (σ : ℝ) (hσ : 0 < σ) (d n : ℕ) :
    SatisfiesSDPI (paramSampleLaw (gaussPrior σ d) gaussLocation n)
        ((n : ℝ) * σ ^ 2 / (1 + (n : ℝ) * σ ^ 2)) ∧
      ∀ {Y : Type} [MeasurableSpace Y] (A : DPVerify.RandAlg (Fin d → ℝ) Y n),
        infoParam A (gaussPrior σ d) gaussLocation / ENNReal.ofReal ((n : ℝ) * σ ^ 2) ≤
          memAvg A (gaussPrior σ d) gaussLocation := by sorry

end MemoSDPI.Main
