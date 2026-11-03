-- Prove2me | Theorems.Thm_HedgeContract_OPE_lemma_6_3_lower
-- name    : HedgeContract.OPE.lemma_6_3_lower
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T04:06:36.883405+00:00
-- url     : https://prove2.me/theorems/cbe7c0bb-0ab0-4bb4-a9bc-a0f6a0375cae
-- title:
--   Lemma 6.3 (lower bound), p. 34 — the immediate lump-sum payout is admissible with payoff δΦ − δy
-- statement:
--   Assume the standing model bounds and parts (1), (2), and (6) of Assumption 6.2: $r>\delta$, $\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}(A^*(Z)-g(Z,\zeta))\ge0$, and $\delta\Phi\le\mu$. Work on a probability space carrying the two independent standard Brownian motions of the reduced model, with their natural filtration.
--
--   For every initial promise $y\ge0$ there is an admissible principal control $(Z,\zeta,I)$, with agent continuation value $Y$ following the dynamics (21) from $Y_{0-}=y$, whose payoff equals
--
--   $$\underline W(y)=\delta\Phi-\delta y.$$
--
--   Concretely, paying the agent the lump sum $\Delta I_0=y$ at time zero drives $Y_0$ to zero, so the project is liquidated immediately and the principal receives $\delta\Phi$ minus the discounted payment $\delta y$.
--
--   This is the lower-bound half of the first assertion of Lemma 6.3. It shows in particular that the admissible payoff set is nonempty, so the principal's value is well defined and bounded below by $\underline W$.
--
--   **Formalization Note.** Admissibility, the Stieltjes payment measure, the liquidation time $\tau=\inf\{t:Y_t\le0\}$ and the payoff are those of `Definitions.Def_HedgeContract_OPE_Model`; the hypotheses repeat those of `HedgeContract.OPE.lemma_6_3_bounds`.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), Lemma 6.3, p. 33 (PDF 35); lower-bound argument on p. 34 (PDF 36): "the principal can pay the agent a lump-sum transfer ΔI0 = y so that the agent quits immediately. This suboptimal strategy gives value δΦ − δy"

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Lemma 6.3, lower bound: the immediate lump-sum payout `ΔI₀ = y` is admissible and has
payoff `W̲(y) = δΦ - δy`. -/
theorem lemma_6_3_lower (P : Params) (hP : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (h1 : P.δ < P.r) (h2 : 0 ≤ netSup P) (h6 : P.δ * P.Φ ≤ P.mu) :
    ∀ y : ℝ, 0 ≤ y →
      ∃ C : Contract Ω, C.Admissible P P₀ B hB y ∧ C.payoff P P₀ = Wlow P y := by sorry

end HedgeContract.OPE
