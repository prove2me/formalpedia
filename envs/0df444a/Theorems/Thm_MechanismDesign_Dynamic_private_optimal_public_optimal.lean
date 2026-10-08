-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_private_optimal_public_optimal
-- name    : MechanismDesign.Dynamic.private_optimal_public_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:12:05.257238+00:00
-- url     : https://prove2.me/theorems/95adfd42-3cad-439d-b931-c1d0c8a9b5be
-- title:
--   Proposition 11.10 -- a mechanism optimal with private $\gamma$ is optimal with public $\gamma$
-- statement:
--   Consider the sequential screening model in the representation $\gamma=F(\theta\mid\tau)$, suppose Assumption 11.1 holds, and let $f(\theta\mid\tau)$ and $\partial F(\theta\mid\tau)/\partial\tau$ be continuous in $(\tau,\theta)$. If the mechanism $(\tilde q(\tau,\gamma),\tilde t(\tau,\gamma))$ is optimal when $\gamma$ is privately observable, then it is also optimal when $\gamma$ is publicly observable.
--
--   Hence the privacy of the buyer's additional ex post information $\gamma$ costs the seller nothing: information rents come only from the ex ante type. The converse fails (p.223): with public $\gamma$, incentive compatibility pins down transfers only in expectation over $\gamma$.
--
--   **Formalization Note** "Optimal when $\gamma$ is privately observable" means that the direct mechanism $q(\tau,\theta)=\tilde q(\tau,F(\theta\mid\tau))$, $t(\tau,\theta)=\tilde t(\tau,F(\theta\mid\tau))$ is optimal in the sequential screening model; "optimal when $\gamma$ is publicly observable" means maximal expected revenue among admissible mechanisms that are incentive-compatible with observable $\gamma$ and individually rational. The continuity of the densities is the regularity of pp.217–221 (see Proposition 11.9).
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.223, Proposition 11.10

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening
import Definitions.Def_MechanismDesign_Dynamic_ObservableGamma

namespace MechanismDesign.Dynamic

/-- **Proposition 11.10**, p.223. Suppose Assumption 11.1 holds (and `f(θ|τ)`, `∂F(θ|τ)/∂τ` are
continuous on `[τ̲, τ̄] × [θ̲, θ̄]`). Then if the mechanism `(q̃(τ, γ), t̃(τ, γ))` is optimal when
`γ` is privately observable, it is also optimal when `γ` is publicly observable. -/
theorem private_optimal_public_optimal {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (hA : E.Assumption11_1) (hreg : E.ContinuousDensities) (m : GammaMechanism τlo τhi)
    (hpriv : m.IsOptimalPrivate E) :
    m.IsOptimalPublic E := by sorry

end MechanismDesign.Dynamic
