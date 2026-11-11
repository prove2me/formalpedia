-- Prove2me | Theorems.Thm_GEGIAMP_Relative_proposition_7_2
-- name    : GEGIAMP.Relative.proposition_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:51:49.849173+00:00
-- url     : https://prove2.me/theorems/815efc36-d6af-4efc-8046-bd0c39ef2394
-- title:
--   Proposition 7.2 — quantitative bounds near the terminal time
-- statement:
--   There is a universal $K_\kappa\ge1$ such that, for $0\le t<1$: $\int_t^1g\le K_\kappa r_t^{3/2}\sqrt{\ell_t}$, $g(t)\le K_\kappa\sqrt{r_t\ell_t}$ (7.9); $\gamma(t),\ \|a(t,\cdot)\|_\infty\le K_\kappa\sqrt{\Lambda(t)}$, $4\|a(t,\cdot)\|_\infty^2\le K_\kappa\Lambda(t)$ (7.10); $\|a_x(t,\cdot)\|_\infty\le K_\kappa\Lambda(t)$, $\|a_{xx}(t,\cdot)\|_\infty\le K_\kappa\Lambda(t)^{3/2}$ (7.11). Also $g(1-)=0$, $\int_0^1\gamma=1$, $\int_0^T\Lambda=(L_\tau^2-1)/2$ and $\int_0^T\Lambda^p\le K_pL_\tau^p\tau^{1-p}$ for $p>1$ (7.12), and $\int_0^1r_t^{-p}\ell_t^j\,dt<\infty$ for $p<1$, $j\ge0$ (7.13).
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - encoding: ‖a(t,·)‖_∞ ≤ b (supremum over x) → ∀ x, |a(t,x)| ≤ b (likewise for aₓ, aₓₓ); reason: the same bound
--   - reading: t in (7.9)–(7.11) (domain not restated) → every 0 ≤ t < 1; reason: the bounds concern times below the terminal time
--   - generalization: (7.12) for the cutoff τ of (6.1), T = 1 − τ → every τ ∈ (0, 1), with K_p independent of τ; reason: both are explicit calculus facts valid on (0, 1); the cutoff of (6.1) lies in (0, 1/2]
--   - generalization: (7.13) for j ≥ 0 → every real j ≥ 0; reason: covers the integer exponents; the integral is finite for every real j ≥ 0 when p < 1
--   - encoding: ∫_0^1 r_t^{−p} ℓ_t^j dt < ∞ → IntegrableOn of the integrand on [0, 1); reason: the integrand is nonnegative, so finiteness is integrability
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Proposition 7.2, p. 22

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Model

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Proposition 7.2** (quantitative bounds near the terminal time; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 22).
There is a universal `K_κ ≥ 1` such that for `0 ≤ t < 1`, with `r_t = 1 − t`,
`ℓ_t = log(e/r_t)`, `Λ = ℓ/r`: (7.9) `∫_t^1 g ≤ K_κ r_t^{3/2} √ℓ_t`, `g(t) ≤ K_κ √(r_t ℓ_t)`;
(7.10) `γ(t), ‖a(t,·)‖_∞ ≤ K_κ √Λ(t)`, `4‖a(t,·)‖²_∞ ≤ K_κ Λ(t)`; (7.11)
`‖aₓ(t,·)‖_∞ ≤ K_κ Λ(t)`, `‖aₓₓ(t,·)‖_∞ ≤ K_κ Λ(t)^{3/2}`. Also `g(1−) = 0`, `∫_0^1 γ = 1`,
(7.12) `∫_0^T Λ = (L_τ² − 1)/2` and, for `p > 1`, `∫_0^T Λ^p ≤ K_p L_τ^p τ^{1−p}`
(`T = 1 − τ`), and (7.13) `∫_0^1 r_t^{−p} ℓ_t^j dt < ∞` for `p < 1`, `j ≥ 0`. -/
theorem proposition_7_2 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (X : ℝ≥0 → Ω → ℝ) (hX : IsDiffusion W γ X) :
    ∃ Kκ : ℝ, 1 ≤ Kκ ∧
      (∀ t : ℝ, 0 ≤ t → t < 1 →
        -- (7.9)
        (∫ s in t..1, gFun W γ X s) ≤ Kκ * rr t ^ (3 / 2 : ℝ) * Real.sqrt (ell t) ∧
        gFun W γ X t ≤ Kκ * Real.sqrt (rr t * ell t) ∧
        -- (7.10)
        gam γ t ≤ Kκ * Real.sqrt (Lam t) ∧
        (∀ x : ℝ, |aF W γ t x| ≤ Kκ * Real.sqrt (Lam t)) ∧
        (∀ x : ℝ, 4 * aF W γ t x ^ 2 ≤ Kκ * Lam t) ∧
        -- (7.11)
        (∀ x : ℝ, |axF W γ t x| ≤ Kκ * Lam t) ∧
        (∀ x : ℝ, |axxF W γ t x| ≤ Kκ * Lam t ^ (3 / 2 : ℝ))) ∧
      Filter.Tendsto (gFun W γ X) (𝓝[<] 1) (𝓝 0) ∧
      (∫ t in (0 : ℝ)..1, gam γ t) = 1 ∧
      -- (7.12)
      (∀ τ : ℝ, 0 < τ → τ < 1 → (∫ t in (0 : ℝ)..(1 - τ), Lam t) = (Lg τ ^ 2 - 1) / 2) ∧
      (∀ p : ℝ, 1 < p → ∃ Kp : ℝ, ∀ τ : ℝ, 0 < τ → τ < 1 →
        (∫ t in (0 : ℝ)..(1 - τ), Lam t ^ p) ≤ Kp * Lg τ ^ p * τ ^ (1 - p)) ∧
      -- (7.13)
      (∀ p j : ℝ, p < 1 → 0 ≤ j →
        IntegrableOn (fun t => rr t ^ (-p) * ell t ^ j) (Set.Ico (0 : ℝ) 1)) := by sorry

end GEGIAMP.Relative
