-- Prove2me | Theorems.Thm_ModelRiskOT_PrimalOpt_proposition_9
-- name    : ModelRiskOT.PrimalOpt.proposition_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:17:46.977754+00:00
-- url     : https://prove2.me/theorems/f7b6a73f-0c53-4ba8-b15b-7bf03c5e0ac4
-- title:
--   Proposition 9 — (P-Compactness) and (P-USC) imply a primal optimizer exists
-- statement:
--   Let $S$ be a Polish space, $\mu$ a probability measure on $S$, $\delta>0$, and let $c$ and $f$ satisfy (A1) and (A2). Assume the standing assumption of §5: $(\lambda^*,\varphi_{\lambda^*})\in\Lambda_{c,f}$ is a dual optimal pair with
--   $$I=J=J(\lambda^*,\varphi_{\lambda^*})<\infty.$$
--   If $(c,f)$ has Property (P-Compactness) at $\lambda^*$ and Property (P-USC), then there is a primal optimizer $\pi^*\in\Phi_{\mu,\delta}$ with
--   $$I(\pi^*)=I=J=J(\lambda^*,\varphi_{\lambda^*}).$$
--
--   The primal feasible set is in general not weakly compact, and the supremum need not be attained (Example 2 of the paper); the two properties replace compactness and upper semicontinuity.
--
--   **Formalization Note** The equality $I=J$ is Theorem 1(a) of the paper, which is not assumed proved here; it enters as the hypothesis of the section's standing assumption, together with the dual optimality $J=J(\lambda^*,\varphi_{\lambda^*})$ and finiteness. No sign condition on $\lambda^*$ beyond $\lambda^*\ge0$ (part of $\Lambda_{c,f}$) is assumed.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 26, Proposition 9 (with the standing assumption of §5)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_PCompactness
import Definitions.Def_ModelRiskOT_PrimalOpt_PUSC

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **Proposition 9** (§5, p. 26). Assume (A1), (A2) and the standing assumption of §5:
`(λ*, φ_{λ*}) ∈ Λ_{c,f}` is a dual optimal pair with `I = J = J(λ*, φ_{λ*}) < ∞` (the identity
`I = J` is Theorem 1(a), taken here as a hypothesis). If (P-Compactness) holds for `λ*` and (P-USC)
holds, there is a primal optimizer `π* ∈ Φ_{μ,δ}` with `I(π*) = I = J = J(λ*, φ_{λ*})`. -/
theorem proposition_9 {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S]
    [BorelSpace S] (c : S → S → ℝ) (f : S → ℝ) (μ : Measure S) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ)
    (lam : ℝ) (hfeas : (lam, phiLam c f lam) ∈ dualFeasible c f)
    (hIJ : ModelRiskOT.Duality.primalValue c f μ δ = ModelRiskOT.Duality.dualValue c f μ δ)
    (hopt : ModelRiskOT.Duality.dualValue c f μ δ = ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam))
    (hfin : ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam) < ⊤)
    (hP1 : PCompactness c f μ lam) (hP2 : PUSC c f μ δ) :
    ∃ πstar ∈ ModelRiskOT.Duality.primalFeasible c μ δ,
      ModelRiskOT.Duality.primalObj f πstar = ModelRiskOT.Duality.primalValue c f μ δ ∧ ModelRiskOT.Duality.primalValue c f μ δ = ModelRiskOT.Duality.dualValue c f μ δ ∧
        ModelRiskOT.Duality.dualValue c f μ δ = ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam) := by sorry

end ModelRiskOT.PrimalOpt
