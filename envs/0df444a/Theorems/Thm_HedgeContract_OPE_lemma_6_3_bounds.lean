-- Prove2me | Theorems.Thm_HedgeContract_OPE_lemma_6_3_bounds
-- name    : HedgeContract.OPE.lemma_6_3_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:52.010183+00:00
-- url     : https://prove2.me/theorems/86baf48b-a468-472b-9c00-1842d7fa2909
-- title:
--   Lemma 6.3, p. 33 (PDF 35) — value bounds
-- statement:
--   Assume the standing model bounds and parts (1), (2), and (6) of Assumption 6.2: $r>\delta$, $\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}(A^*(Z)-g(Z,\zeta))\ge0$, and $\delta\Phi\le\mu$. On a probability space carrying the two independent Brownian shocks of the model, the admissible payoff set from every initial promise $y\ge0$ is nonempty and bounded above. Its supremum $W(y)$ obeys
--
--   $$\underline W(y)=\delta\Phi-\delta y\le W(y)\le\overline W(y)=\mu-\delta y+\sup_{(Z,\zeta)\in\mathcal Z\times\Gamma}(A^*(Z)-g(Z,\zeta)).$$
--
--   These bounds establish that the principal's real-valued control value is well defined. They are the first assertion of Lemma 6.3; its viscosity assertion is a separate target.
--
--   **Formalization Note.** Nonemptiness and boundedness are explicit so the real supremum cannot take a default value on a bad feasible set.
-- source:
--   Huang, Ju & Xing, Optimal Contracting with Unobservable Managerial Hedging, working paper (Nov. 14, 2017), p. 33 (PDF 35), Lemma 6.3, first assertion

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false

namespace HedgeContract.OPE
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- The bounds in the first assertion of Lemma 6.3. -/
theorem lemma_6_3_bounds (P : Params) (hP : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (h1 : P.δ < P.r) (h2 : 0 ≤ netSup P) (h6 : P.δ * P.Φ ≤ P.mu) :
    ∀ y : ℝ, 0 ≤ y →
      (valueSet P P₀ B hB y).Nonempty ∧
      BddAbove (valueSet P P₀ B hB y) ∧
      Wlow P y ≤ sSup (valueSet P P₀ B hB y) ∧
      sSup (valueSet P P₀ B hB y) ≤ Wbar P y := by sorry

end HedgeContract.OPE
