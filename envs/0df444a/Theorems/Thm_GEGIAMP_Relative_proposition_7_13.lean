-- Prove2me | Theorems.Thm_GEGIAMP_Relative_proposition_7_13
-- name    : GEGIAMP.Relative.proposition_7_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:55:03.842064+00:00
-- url     : https://prove2.me/theorems/b0c41767-0437-4826-a1ab-43966b04cf45
-- title:
--   Proposition 7.13 — unit normalization factors satisfy (7.116)
-- statement:
--   After fixing the grid, quadrature and tolerance constants, there is a universal $\varepsilon_0>0$ such that $\omega_k=1$ satisfies (7.116), with $\nu=c_\nu\varepsilon/\log(4d)$ from (6.18), for every $0<\varepsilon\le\varepsilon_0$. This accuracy threshold is independent of $N$ and $\alpha$.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - reading: "after fixing the grid, quadrature, and tolerance constants" → for every positive (c_τ, c_h, c_B, c_q, K_R) with K_R chosen as in (6.5) (a² ≤ K_R Λ on [0,1) × ℝ) and every c_ν > 0, ∃ ε₀; reason: these are the constants named; K_R’s defining property is stated with (6.5)
--   - encoding: "independent of N and α" → ε₀ is chosen before ε and the statement has no N or α; reason: the same independence
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Proposition 7.13, p. 38

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Proposition 7.13** (Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 38). After fixing the grid, quadrature and tolerance
constants, there is a universal `ε₀ > 0` such that `ω_k = 1` satisfies (7.116), with
`ν = c_ν ε/log(4d)` from (6.18), for every `0 < ε ≤ ε₀`; this threshold is independent of `N`
and `α`. Here `ρ_k` are the factors (6.16) of the scalar recursion (6.7) with the quadrature
values (6.6) on the grid (6.1)–(6.2), and `K_R` is chosen as in (6.5). -/
theorem proposition_7_13 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (κ : AlgConsts) (hκ : κ.Pos)
    (hKR : KRValid W γ κ) (cν : ℝ) (hcν : 0 < cν) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      Cond7116 (fun _ => 1)
        (rhoOf (mF W γ) (aF W γ) (params κ ε).h (Gq (gam γ) κ ε) (params κ ε).K)
        (nuOf cν ε (params κ ε).d) (params κ ε).K := by sorry

end GEGIAMP.Relative
