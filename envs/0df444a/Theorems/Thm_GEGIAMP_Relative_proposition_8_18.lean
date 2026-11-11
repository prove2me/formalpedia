-- Prove2me | Theorems.Thm_GEGIAMP_Relative_proposition_8_18
-- name    : GEGIAMP.Relative.proposition_8_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:51:31.542911+00:00
-- url     : https://prove2.me/theorems/34382ac9-f2a8-4de1-af70-c9ad200240ab
-- title:
--   Proposition 8.18 — finite-size optimum bound
-- statement:
--   For every $N$, $\mathbb E\,\mathrm{OPT}_N/N\le P^*$, and $\mathbb P\{\mathrm{OPT}_N/N>P^*+u\}\le e^{-Nu^2}$ for $u>0$ (8.87), for $A\sim$ GOE$(N)$.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - reading: "for every N" → every N ≥ 1; reason: OPT_N/N needs N ≥ 1
--   - encoding: P{OPT_N/N > P* + u} → outer GOE(N) measure of that set; reason: no measurability side condition
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Proposition 8.18, p. 59

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Model

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Proposition 8.18** (finite-size optimum bound; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 59). For every `N`,
`E OPT_N/N ≤ P*`, and `P{OPT_N/N > P* + u} ≤ e^{−N u²}` for `u > 0` (8.87), for
`A ∼ GOE(N)`. -/
theorem proposition_8_18 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (N : ℕ) (hN : 1 ≤ N) :
    (∫ A, OPT A ∂(RandMatDisc.goe N)) / N ≤ Pstar W γ ∧
    ∀ u : ℝ, 0 < u →
      RandMatDisc.goe N {A | Pstar W γ + u < OPT A / N} ≤ ENNReal.ofReal (Real.exp (-(N * u ^ 2))) := by sorry

end GEGIAMP.Relative
