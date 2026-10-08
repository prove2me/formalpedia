-- Prove2me | Theorems.Thm_ModelRiskOT_Duality_phiLam_universallyMeasurable
-- name    : ModelRiskOT.Duality.phiLam_universallyMeasurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:16:03.364342+00:00
-- url     : https://prove2.me/theorems/b4ba84de-5c6f-4fd5-962e-45d6f9d9d6a3
-- title:
--   §4.2 — $\varphi_\lambda$ is universally measurable
-- statement:
--   Let $S$ be a Polish space, $c$ a cost satisfying (A1), $f:S\to\mathbb R$ upper semicontinuous and $\lambda\ge0$. Then the function
--
--   $$\varphi_\lambda(x)=\sup_{y\in S}\{f(y)-\lambda c(x,y)\}$$
--
--   belongs to $m\mathcal U(S;\bar{\mathbb R})$: for every Borel set $B\subseteq[-\infty,\infty]$, the set $\varphi_\lambda^{-1}(B)$ is universally measurable.
--
--   $\varphi_\lambda$ need not be Borel measurable; this result is what makes $(\lambda,\varphi_\lambda)$ a member of the dual feasible set $\Lambda_{c,f}$ in Theorem 1(b).
--
--   **Formalization Note** The paper states this under (A1) and (A2); the integrability of $f$ in (A2) refers to a measure $\mu$ that plays no role here and is not assumed.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 20, §4.2 (unnumbered)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_AssumptionA1
import Definitions.Def_ModelRiskOT_Duality_dualFeasible
import Definitions.Def_ModelRiskOT_Duality_phiLam

namespace ModelRiskOT.Duality

/-- **Measurability of φ_λ** (Blanchet & Murthy, arXiv:1604.01446v2, §4.2, p. 20; unnumbered).
Under (A1), with `f` upper semicontinuous and `λ ≥ 0`, the function
`φ_λ(x) = sup_{y ∈ S} {f(y) − λ c(x, y)}` belongs to `mU(S; R̄)`: the preimage of every Borel
subset of `[−∞, ∞]` is universally measurable. -/
theorem phiLam_universallyMeasurable {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (c : S → S → ℝ) (hc : AssumptionA1 c) (f : S → ℝ) (hf_usc : UpperSemicontinuous f)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    IsUnivMeasurableEReal (phiLam c f lam) := by sorry

end ModelRiskOT.Duality
