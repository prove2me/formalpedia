-- Prove2me | Theorems.Thm_HedgeContract_OPE_lemma_6_3_upper
-- name    : HedgeContract.OPE.lemma_6_3_upper
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T04:06:41.79748+00:00
-- url     : https://prove2.me/theorems/b0a0c845-3606-4e62-8f26-77a6a7249b94
-- title:
--   Lemma 6.3 (upper bound), pp. 33–34 — every admissible payoff is at most μ − δy + sup(A* − g)
-- statement:
--   Assume the standing model bounds and parts (1), (2), and (6) of Assumption 6.2: $r>\delta$, $\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}(A^*(Z)-g(Z,\zeta))\ge0$, and $\delta\Phi\le\mu$. Work on a probability space carrying the two independent standard Brownian motions of the reduced model, with their natural filtration.
--
--   For every initial promise $y\ge0$ and every admissible principal control $(Z,\zeta,I)$ with agent continuation value $Y$ following (21) from $Y_{0-}=y$ and satisfying the transversality condition (57), the principal's payoff
--
--   $$\mathbb E\Big[\delta\int_0^\tau e^{-\delta t}\big(\mu+A^*(Z_t)\big)\,dt-\delta\int_{[0,\tau]}e^{-\delta t}\,dI_t+\delta e^{-\delta\tau}\Phi\,\mathbf 1_{\{\tau<\infty\}}\Big]$$
--
--   is at most
--
--   $$\overline W(y)=\mu-\delta y+\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}\big(A^*(Z)-g(Z,\zeta)\big).$$
--
--   This is the upper-bound half of the first assertion of Lemma 6.3. It shows that the admissible payoff set is bounded above, so the principal's real-valued value is well defined and dominated by $\overline W$.
--
--   **Formalization Note.** Admissibility, the Stieltjes payment measure (which charges the time-zero lump sum), the liquidation time $\tau=\inf\{t:Y_t\le0\}$ and the payoff are those of `Definitions.Def_HedgeContract_OPE_Model`; the hypotheses repeat those of `HedgeContract.OPE.lemma_6_3_bounds`.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), Lemma 6.3, p. 33 (PDF 35); upper-bound (supersolution + Itô formula + transversality (57)) argument on p. 34 (PDF 36)

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Lemma 6.3, upper bound: every admissible payoff from `y` is at most
`W̄(y) = μ - δy + sup (A* - g)`. -/
theorem lemma_6_3_upper (P : Params) (hP : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (h1 : P.δ < P.r) (h2 : 0 ≤ netSup P) (h6 : P.δ * P.Φ ≤ P.mu) :
    ∀ y : ℝ, 0 ≤ y → ∀ C : Contract Ω, C.Admissible P P₀ B hB y →
      C.payoff P P₀ ≤ Wbar P y := by sorry

end HedgeContract.OPE
