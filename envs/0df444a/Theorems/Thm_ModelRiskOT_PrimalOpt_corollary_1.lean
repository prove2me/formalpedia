-- Prove2me | Theorems.Thm_ModelRiskOT_PrimalOpt_corollary_1
-- name    : ModelRiskOT.PrimalOpt.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:51:32.848975+00:00
-- url     : https://prove2.me/theorems/32530b28-3917-4de7-991b-aa6599783bc6
-- title:
--   Corollary 1 — a worst-case transport plan exists in a locally compact normed space under (A1)–(A4) when λ* > 0
-- statement:
--   Let $E$ be a real normed space that is locally compact in the topology of its norm $\|\cdot\|$, with its Borel $\sigma$-algebra; let $\mu$ be a probability measure on $E$ and $\delta>0$. Let the cost $c$ and the function $f$ satisfy Assumptions (A1)–(A4). Assume the standing assumption of §5: $(\lambda^*,\varphi_{\lambda^*})\in\Lambda_{c,f}$ is a dual optimal pair with
--   $$I=J=J(\lambda^*,\varphi_{\lambda^*})<\infty.$$
--   If $\lambda^*>0$, there is a primal optimizer $\pi^*\in\Phi_{\mu,\delta}$, i.e. a transport plan with first marginal $\mu$ and cost $\int c\,d\pi^*\le\delta$, such that
--   $$I(\pi^*)=I=J=J(\lambda^*,\varphi_{\lambda^*}).$$
--
--   Its second marginal is then a worst-case model: it attains $\sup\{\int f\,d\nu: d_c(\mu,\nu)\le\delta\}$.
--
--   **Formalization Note** The equality $I=J$ is Theorem 1(a) of the paper, not assumed proved here; it is a hypothesis, as in the paper's standing assumption for §5. The condition $\lambda^*>0$ cannot be dropped: Example 2 of the paper has $\lambda^*=0$ and no primal optimizer. The instance `PolishSpace E` is redundant (a locally compact real normed space is finite-dimensional) and is included because the §2 objects are posed on a Polish space; local compactness is kept as the paper states it.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 27, Corollary 1 (with the standing assumption of §5, p. 26)

import Mathlib
import Definitions.Def_ModelRiskOT_PrimalOpt_Basic
import Definitions.Def_ModelRiskOT_PrimalOpt_GrowthAssumptions

namespace ModelRiskOT.PrimalOpt

open MeasureTheory

/-- **Corollary 1** (§5, p. 27). Let `E` be a real normed space that is locally compact in its norm
topology, with its Borel σ-algebra, and let `c`, `f` satisfy (A1)–(A4). Assume the standing
assumption of §5: `(λ*, φ_{λ*}) ∈ Λ_{c,f}` is a dual optimal pair with
`I = J = J(λ*, φ_{λ*}) < ∞` (the identity `I = J` is Theorem 1(a), taken here as a hypothesis).
If `λ* > 0`, there is a primal optimizer `π* ∈ Φ_{μ,δ}` with `I(π*) = I = J = J(λ*, φ_{λ*})`. -/
theorem corollary_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : E → E → ℝ) (f : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (δ : ℝ) (hδ : 0 < δ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ)
    (hA3 : AssumptionA3 c) (hA4 : AssumptionA4 c f)
    (lam : ℝ) (hlam : 0 < lam) (hfeas : (lam, phiLam c f lam) ∈ dualFeasible c f)
    (hIJ : ModelRiskOT.Duality.primalValue c f μ δ = ModelRiskOT.Duality.dualValue c f μ δ)
    (hopt : ModelRiskOT.Duality.dualValue c f μ δ = ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam))
    (hfin : ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam) < ⊤) :
    ∃ πstar ∈ ModelRiskOT.Duality.primalFeasible c μ δ,
      ModelRiskOT.Duality.primalObj f πstar = ModelRiskOT.Duality.primalValue c f μ δ ∧ ModelRiskOT.Duality.primalValue c f μ δ = ModelRiskOT.Duality.dualValue c f μ δ ∧
        ModelRiskOT.Duality.dualValue c f μ δ = ModelRiskOT.Duality.dualObj μ δ lam (phiLam c f lam) := by sorry

end ModelRiskOT.PrimalOpt
