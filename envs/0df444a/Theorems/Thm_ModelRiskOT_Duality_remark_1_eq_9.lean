-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_remark_1_eq_9
-- name    : ModelRiskOT.Duality.remark_1_eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:39:38.72679+00:00
-- url     : https://prove2.me/theorems/9fa9e17a-52d9-4206-b8b2-e4040d7398c7
-- title:
--   Remark 1, (9) — $I=\inf_{\lambda\ge0}\{\lambda\delta+E_\mu[\sup_y\{f(y)-\lambda c(X,y)\}]\}$
-- statement:
--   Let $S$ be a Polish space, $\mu$ a Borel probability measure on $S$, $c : S\times S\to[0,\infty)$ a lower semicontinuous cost with $c(x,y)=0$ if and only if $x=y$ (Assumption (A1)), $f : S\to\mathbb R$ upper semicontinuous and $\mu$-integrable (Assumption (A2)), and $\delta>0$. Then
--
--   $$I=\inf_{\lambda\ge0}\Big\{\lambda\delta+E_\mu\Big[\sup_{y\in S}\{f(y)-\lambda c(X,y)\}\Big]\Big\},$$
--
--   where $X\sim\mu$. The right-hand side is a one-dimensional reformulation of the dual problem: it only involves the baseline measure $\mu$. The proof of Theorem 1(a) establishes it, and the proof of Theorem 1(b) starts from it.
--
--   **Formalization Note** The space $S$ is a Polish space with its Borel σ-algebra; the cost $c$ is real-valued and written curried, $c\,x\,y = c(x,y)$; (A1) is the structure `AssumptionA1`; (A2) is the pair of hypotheses `UpperSemicontinuous f` and `Integrable f μ`. Values that can be infinite ($I$, $J$, $I(\pi)$, $J(\lambda,\varphi)$, $\varphi_\lambda$) live in `EReal`; an integral of an extended-real function is $\int\varphi^+ - \int\varphi^-$ with lower Lebesgue integrals, and $\infty-\infty$ evaluates to $-\infty$, so a coupling with $\int f^-\,d\pi=\infty$ never raises the primal supremum (the paper's footnote 2 reading).
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 7, Remark 1, Eq. (9)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_ModelRiskOT_Duality_dualValue
import Definitions.Def_ModelRiskOT_Duality_phiLam

open MeasureTheory

namespace ModelRiskOT.Duality

/-- **Remark 1, (9)** (Blanchet & Murthy, arXiv:1604.01446v2, p. 7). Under (A1) and (A2), with
`δ > 0`: `I = inf_{λ ≥ 0} {λδ + E_μ[sup_{y ∈ S} {f(y) − λ c(X, y)}]}`. -/
theorem remark_1_eq_9 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (c : S → S → ℝ) (hc : AssumptionA1 c)
    (f : S → ℝ) (hf_usc : UpperSemicontinuous f) (hf_int : Integrable f μ)
    (δ : ℝ) (hδ : 0 < δ) :
    primalValue c f μ δ = ⨅ lam ∈ Set.Ici (0 : ℝ), dualObj μ δ lam (phiLam c f lam) := by sorry

end ModelRiskOT.Duality
