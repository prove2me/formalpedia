-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_proposition_6
-- name    : ModelRiskOT.Duality.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:38:51.103615+00:00
-- url     : https://prove2.me/theorems/038cd8d6-fe2e-4776-bb59-87ee00958006
-- title:
--   Proposition 6 — strong duality and a primal optimizer on compact $S$ with lsc cost
-- statement:
--   Let $S$ be a compact Polish space, $\mu$ a Borel probability measure on $S$, $c$ a cost satisfying (A1), $f:S\to\mathbb R$ upper semicontinuous and $\mu$-integrable (A2), and $\delta>0$. Then
--
--   $$I=J,$$
--
--   and there is a primal optimizer $\pi^*\in\Phi_{\mu,\delta}$ with $I(\pi^*)=I$.
--
--   Proposition 6 removes the continuity of the cost from Proposition 5; it is applied on compact pieces $S_n\times S_n$ in the proof of Proposition 7.
--
--   **Formalization Note** The space $S$ is a Polish space with its Borel σ-algebra; the cost $c$ is real-valued and written curried, $c\,x\,y = c(x,y)$; (A1) is the structure `AssumptionA1`; (A2) is the pair of hypotheses `UpperSemicontinuous f` and `Integrable f μ`. Values that can be infinite ($I$, $J$, $I(\pi)$, $J(\lambda,\varphi)$, $\varphi_\lambda$) live in `EReal`; an integral of an extended-real function is $\int\varphi^+ - \int\varphi^-$ with lower Lebesgue integrals, and $\infty-\infty$ evaluates to $-\infty$, so a coupling with $\int f^-\,d\pi=\infty$ never raises the primal supremum (the paper's footnote 2 reading).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 17, §4.1, Proposition 6

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_ModelRiskOT_Duality_dualValue

open MeasureTheory

namespace ModelRiskOT.Duality

/-- **Proposition 6** (Blanchet & Murthy, arXiv:1604.01446v2, §4.1, p. 17). Let `S` be a compact
Polish space, `f` satisfy (A2) and `c` satisfy (A1). Then `I = J`, and a primal optimizer
`π* ∈ Φ_{μ,δ}` with `I(π*) = I` exists. -/
theorem proposition_6 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [CompactSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (δ : ℝ) (hδ : 0 < δ) :
    primalValue c f μ δ = dualValue c f μ δ ∧
      ∃ π ∈ primalFeasible c μ δ, primalObj f π = primalValue c f μ δ := by sorry

end ModelRiskOT.Duality
