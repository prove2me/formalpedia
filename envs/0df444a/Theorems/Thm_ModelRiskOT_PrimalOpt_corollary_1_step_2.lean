-- Prove2me | Theorems.Thm_ModelRiskOT_PrimalOpt_corollary_1_step_2
-- name    : ModelRiskOT.PrimalOpt.corollary_1_step_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:16:28.210225+00:00
-- url     : https://prove2.me/theorems/53b37e01-a1ee-4011-bd6a-060522cdec6d
-- title:
--   Proof of Corollary 1, Step 2 (pp. 28–29) — (A1), (A2), (A4) and I < ∞ give (P-USC)
-- statement:
--   Let $E$ be a real normed space that is locally compact in its norm topology, with its Borel $\sigma$-algebra, let $\mu$ be a probability measure on $E$ and $\delta>0$. Let $c$ and $f$ satisfy (A1), (A2) and (A4), and assume $I<\infty$. Then $(c,f)$ has Property (P-USC): for every sequence $(\pi_n)\subseteq\Phi'_{\mu,\delta}$ with $\pi_n\Rightarrow\pi^*\in\Phi_{\mu,\delta}$,
--   $$\limsup_{n\to\infty}\int f(y)\,d\pi_n(x,y)\le\int f(y)\,d\pi^*(x,y).\tag{40}$$
--
--   This is the second verification in the proof of Corollary 1; it rests on a uniform integrability property of $f(y)$ under monotone feasible plans.
--
--   **Formalization Note** The finiteness $I<\infty$ is the part of the standing assumption $I=J<\infty$ the step uses. As in Step 1, `PolishSpace E` is redundant for a locally compact real normed space.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, pp. 28–29, proof of Corollary 1, Step 2, Eq. (40)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_PUSC
import Definitions.Def_ModelRiskOT_PrimalOpt_GrowthAssumptions

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **Proof of Corollary 1, Step 2** (pp. 28–29): on a real normed space `E` that is locally
compact, (A1), (A2), (A4), `δ > 0` and `I < ∞` imply (P-USC). -/
theorem corollary_1_step_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : E → E → ℝ) (f : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ)
    (hA4 : AssumptionA4 c f) (hfin : ModelRiskOT.Duality.primalValue c f μ δ < ⊤) :
    PUSC c f μ δ := by sorry

end ModelRiskOT.PrimalOpt
