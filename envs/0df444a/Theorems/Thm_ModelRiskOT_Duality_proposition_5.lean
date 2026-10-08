-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_proposition_5
-- name    : ModelRiskOT.Duality.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:39:04.573583+00:00
-- url     : https://prove2.me/theorems/73e66bf4-f98c-4404-8ebd-a06969252326
-- title:
--   Proposition 5 — strong duality and a primal optimizer on compact $S$ with continuous cost
-- statement:
--   Let $S$ be a compact Polish space, $\mu$ a Borel probability measure on $S$, $c$ a cost satisfying (A1) that is in addition continuous on $S\times S$, $f:S\to\mathbb R$ upper semicontinuous and $\mu$-integrable (A2), and $\delta>0$. Then
--
--   $$I=J,$$
--
--   and there is a primal optimizer $\pi^*\in\Phi_{\mu,\delta}$ with $I(\pi^*)=I$.
--
--   This is the first step of the proof of Theorem 1, obtained from Fenchel duality on $C_b(S\times S)$.
--
--   **Formalization Note** The space $S$ is a Polish space with its Borel σ-algebra; the cost $c$ is real-valued and written curried, $c\,x\,y = c(x,y)$; (A1) is the structure `AssumptionA1`; (A2) is the pair of hypotheses `UpperSemicontinuous f` and `Integrable f μ`. Values that can be infinite ($I$, $J$, $I(\pi)$, $J(\lambda,\varphi)$, $\varphi_\lambda$) live in `EReal`; an integral of an extended-real function is $\int\varphi^+ - \int\varphi^-$ with lower Lebesgue integrals, and $\infty-\infty$ evaluates to $-\infty$, so a coupling with $\int f^-\,d\pi=\infty$ never raises the primal supremum (the paper's footnote 2 reading).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 17, §4.1, Proposition 5

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_ModelRiskOT_Duality_dualValue

open MeasureTheory

namespace ModelRiskOT.Duality

/-- **Proposition 5** (Blanchet & Murthy, arXiv:1604.01446v2, §4.1, p. 17). Let `S` be a compact
Polish space, `c` satisfy (A1) and in addition be continuous, and `f` satisfy (A2). Then `I = J`,
and a primal optimizer `π* ∈ Φ_{μ,δ}` with `I(π*) = I` exists. -/
theorem proposition_5 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [CompactSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (hc_cont : Continuous (fun p : S × S => c p.1 p.2))
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (δ : ℝ) (hδ : 0 < δ) :
    primalValue c f μ δ = dualValue c f μ δ ∧
      ∃ π ∈ primalFeasible c μ δ, primalObj f π = primalValue c f μ δ := by sorry

end ModelRiskOT.Duality
