-- Prove2me | Theorems.Thm_GEGIAMP_Relative_proposition_7_1
-- name    : GEGIAMP.Relative.proposition_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:51:38.208485+00:00
-- url     : https://prove2.me/theorems/37ca42e3-7c5b-4b13-88cc-1b176c299985
-- title:
--   Proposition 7.1 — zero-temperature Parisi diffusion identities
-- statement:
--   Under the standing hypotheses, for a Parisi diffusion $X$ with $M_t=m(t,X_t)$ and $g(t)=\mathbb Ea(t,X_t)$, for $0\le s\le t<1$: $dM_t=a(t,X_t)\,dB_t$, $\mathbb Ea(t,X_t)^2=1$, $a(0,0)=1$ (7.1); $\mathbb E[(M_t-M_s)^2]=t-s$, $g(t)=1-\int_0^t\gamma$, $0\le g\le1$ (7.2). The bounded martingale has an $L^2$ terminal limit $M_1\in\{-1,1\}$. Moreover $P^*=\int_0^1g$ (7.3) and $\mathbb Ea_x(t,X_t)^2=2\gamma(t)\mathbb Ea(t,X_t)^3$ for almost every $t<1$ (7.4).
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - encoding: dM_t = a(t, X_t) dB_t → M_t, M_t B_t − ∫_0^t a(r,X_r) dr and M_t² − ∫_0^t a(r,X_r)² dr are martingales on [0,1) for the natural filtration of B (conditional-expectation identities for 0 ≤ s ≤ t < 1); reason: Mathlib at this revision has no Itô integral; for continuous square-integrable martingales these identities are equivalent to M_t − M_0 = ∫_0^t a dB
--   - encoding: an L² terminal limit M_1 ∈ {−1, 1} → ∃ M₁ with eLpNorm(M_t − M₁, 2) → 0 as t → 1⁻ and M₁ ∈ {−1, 1} almost surely; reason: the same notion
--   - encoding: for almost every t < 1 → for Lebesgue-almost every t ∈ [0, 1); reason: the same notion
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Proposition 7.1, p. 21

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Model

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Proposition 7.1** (zero-temperature Parisi diffusion identities; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 21).
Under Assumption 2.1, for a Parisi diffusion `X` with `M_t = m(t, X_t)` and `g(t) = E a(t, X_t)`:
`dM_t = a(t, X_t) dB_t` (encoded by the three martingale identities below), `E a(t, X_t)² = 1`,
`a(0, 0) = 1`, `E(M_t − M_s)² = t − s`, `g(t) = 1 − ∫_0^t γ`, `0 ≤ g ≤ 1` (for `s ≤ t < 1`); the
bounded martingale has an `L²` terminal limit `M_1 ∈ {−1, 1}`; `P* = ∫_0^1 g`; and
`E aₓ(t, X_t)² = 2γ(t) E a(t, X_t)³` for almost every `t < 1`. -/
theorem proposition_7_1 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (X : ℝ≥0 → Ω → ℝ) (hX : IsDiffusion W γ X) :
    -- dM = a dB: M, M_t B_t − ∫_0^t a(r, X_r) dr and M_t² − ∫_0^t a(r, X_r)² dr are martingales
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
      W.law[Mag W γ X t | brownFiltration W s.toNNReal] =ᵐ[W.law] Mag W γ X s) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
      W.law[fun ω => Mag W γ X t ω * W.B t.toNNReal ω -
          ∫ r in (0 : ℝ)..t, aF W γ r (X r.toNNReal ω) | brownFiltration W s.toNNReal]
        =ᵐ[W.law] fun ω => Mag W γ X s ω * W.B s.toNNReal ω -
          ∫ r in (0 : ℝ)..s, aF W γ r (X r.toNNReal ω)) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
      W.law[fun ω => Mag W γ X t ω ^ 2 -
          ∫ r in (0 : ℝ)..t, aF W γ r (X r.toNNReal ω) ^ 2 | brownFiltration W s.toNNReal]
        =ᵐ[W.law] fun ω => Mag W γ X s ω ^ 2 -
          ∫ r in (0 : ℝ)..s, aF W γ r (X r.toNNReal ω) ^ 2) ∧
    -- (7.1)
    (∀ t : ℝ, 0 ≤ t → t < 1 → ∫ ω, aF W γ t (X t.toNNReal ω) ^ 2 ∂W.law = 1) ∧
    aF W γ 0 0 = 1 ∧
    -- (7.2)
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
      ∫ ω, (Mag W γ X t ω - Mag W γ X s ω) ^ 2 ∂W.law = t - s) ∧
    (∀ t : ℝ, 0 ≤ t → t < 1 → gFun W γ X t = 1 - ∫ r in (0 : ℝ)..t, gam γ r) ∧
    (∀ t : ℝ, 0 ≤ t → t < 1 → 0 ≤ gFun W γ X t ∧ gFun W γ X t ≤ 1) ∧
    -- the L² terminal limit M_1 ∈ {−1, 1}
    (∃ M₁ : Ω → ℝ, Filter.Tendsto (fun t : ℝ => eLpNorm (fun ω => Mag W γ X t ω - M₁ ω) 2 W.law)
        (𝓝[<] 1) (𝓝 0) ∧ ∀ᵐ ω ∂W.law, M₁ ω = 1 ∨ M₁ ω = -1) ∧
    -- (7.3)
    Pstar W γ = ∫ t in (0 : ℝ)..1, gFun W γ X t ∧
    -- (7.4)
    (∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)),
      ∫ ω, axF W γ t (X t.toNNReal ω) ^ 2 ∂W.law =
        2 * gam γ t * ∫ ω, aF W γ t (X t.toNNReal ω) ^ 3 ∂W.law) := by sorry

end GEGIAMP.Relative
