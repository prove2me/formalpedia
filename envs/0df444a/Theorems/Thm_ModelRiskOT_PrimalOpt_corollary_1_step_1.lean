-- Prove2me | Theorems.Thm_ModelRiskOT_PrimalOpt_corollary_1_step_1
-- name    : ModelRiskOT.PrimalOpt.corollary_1_step_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:04:52.680835+00:00
-- url     : https://prove2.me/theorems/5473dea3-4fe3-43f2-a377-4f60a8ad7d74
-- title:
--   Proof of Corollary 1, Step 1 (p. 28) — (A1)–(A4) and λ* > 0 give (P-Compactness)
-- statement:
--   Let $E$ be a real normed space that is locally compact in its norm topology, with its Borel $\sigma$-algebra, and let $\mu$ be a probability measure on $E$. Let $c$ and $f$ satisfy (A1)–(A4) and let $\lambda^*>0$. Then $(c,f)$ has Property (P-Compactness) at $\lambda^*$: for every $\varepsilon>0$ there are a compact $K_\varepsilon$ with $\mu(K_\varepsilon)>1-\varepsilon$ and $\gamma>0$ such that the closure of
--   $$\Gamma_\varepsilon=\bigl\{(x,y)\in K_\varepsilon\times E:\ f(y)-\lambda^*c(x,y)\ge\varphi_{\lambda^*}(x)-\gamma\bigr\}$$
--   is compact.
--
--   This is the first of the two verifications in the proof of Corollary 1.
--
--   **Formalization Note** The step only uses $\varphi_{\lambda^*}\ge f$, which holds by definition, so no dual optimality is assumed. The paper's text concludes "verifying Assumption (A3)", meaning Property 1 (P-Compactness), and writes $f(y)-f(x)\le\varepsilon'c(x,y)$ where (A4) gives $\varepsilon'(1+c(x,y))$; the statement is the step's conclusion. A locally compact real normed space is finite-dimensional, hence complete and separable; the instance `PolishSpace E` is therefore redundant and is included because the definitions of §2 are posed on a Polish space.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 28, proof of Corollary 1, Step 1

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_PCompactness
import Definitions.Def_ModelRiskOT_PrimalOpt_GrowthAssumptions

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **Proof of Corollary 1, Step 1** (p. 28): on a real normed space `E` that is locally compact,
(A1)–(A4) and `λ* > 0` imply (P-Compactness) for `λ*`. -/
theorem corollary_1_step_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : E → E → ℝ) (f : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ) (hA3 : AssumptionA3 c)
    (hA4 : AssumptionA4 c f) (lam : ℝ) (hlam : 0 < lam) :
    PCompactness c f μ lam := by sorry

end ModelRiskOT.PrimalOpt
