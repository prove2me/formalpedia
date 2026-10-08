-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_observable_gamma_envelope
-- name    : MechanismDesign.Dynamic.observable_gamma_envelope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:11:43.824983+00:00
-- url     : https://prove2.me/theorems/be792743-8432-4e99-8d23-00bfddc64ad5
-- title:
--   Proposition 11.9 -- envelope formula with observable $\gamma$
-- statement:
--   Consider the sequential screening model in the representation $\gamma=F(\theta\mid\tau)$, with $f(\theta\mid\tau)$ and $\partial F(\theta\mid\tau)/\partial\tau$ continuous in $(\tau,\theta)$. If an admissible direct mechanism $(\tilde q(\tau,\gamma),\tilde t(\tau,\gamma))$ is incentive-compatible with observable $\gamma$, then for every $\tau\in[\underline\tau,\bar\tau]$
--   $$U(\tau)=U(\underline\tau)+\int_{\underline\tau}^{\tau}\!\int_0^1\frac{\partial F^{-1}(\gamma\mid\hat\tau)}{\partial\tau}\,\tilde q(\hat\tau,\gamma)\,d\gamma\,d\hat\tau,$$
--   where $U(\tau)=\int_0^1[F^{-1}(\gamma\mid\tau)\tilde q(\tau,\gamma)-\tilde t(\tau,\gamma)]\,d\gamma$.
--
--   The formula lets the seller's revenue with public $\gamma$ be written in terms of the allocation rule alone, as in the private case.
--
--   **Formalization Note** The continuity of the densities is the regularity the book invokes on p.217 and uses on pp.220–221 to differentiate $F^{-1}(\gamma\mid\tau)$; with it $F^{-1}(\gamma\mid\cdot)$ is differentiable on $[\underline\tau,\bar\tau]$, and $\partial F^{-1}/\partial\tau$ is its derivative within that interval.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.221, Proposition 11.9

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_ObservableGamma

namespace MechanismDesign.Dynamic

/-- **Proposition 11.9**, p.221. (With `f(θ|τ)` and `∂F(θ|τ)/∂τ` continuous on
`[τ̲, τ̄] × [θ̲, θ̄]`, so that `F⁻¹(γ|τ)` is differentiable in `τ`.) If an (admissible) direct
mechanism `(q̃(τ, γ), t̃(τ, γ))` is incentive-compatible with observable `γ`, then for every
`τ ∈ [τ̲, τ̄]`
`U(τ) = U(τ̲) + ∫_{τ̲}^{τ} ∫_0^1 ∂F⁻¹(γ|τ̂)/∂τ · q̃(τ̂, γ) dγ dτ̂`. -/
theorem observable_gamma_envelope {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (hreg : E.ContinuousDensities) (m : GammaMechanism τlo τhi) (hm : m.Admissible)
    (hic : m.IsICObs E) :
    ∀ τ ∈ Set.Icc τlo τhi,
      m.Uobs E τ = m.Uobs E τlo +
        ∫ τ' in τlo..τ, ∫ γ in (0 : ℝ)..1,
          derivWithin (fun s => E.Finv γ s) (Set.Icc τlo τhi) τ' * m.q τ' γ := by sorry

end MechanismDesign.Dynamic
