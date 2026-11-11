-- Prove2me | Theorems.Thm_GEGIAMP_Relative_lemma_7_10
-- name    : GEGIAMP.Relative.lemma_7_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:54:39.553069+00:00
-- url     : https://prove2.me/theorems/82d85596-9476-4889-b9e9-3003b836f380
-- title:
--   Lemma 7.10 — point quadrature error, work and storage
-- statement:
--   For the quadrature rule (6.6) and every grid cell $[t_k,t_{k+1}]$, $0\le k<K$: $|\Gamma^q_k-\Gamma_k|\le\eta_qh/2$ and $0\le\Gamma^q_k\le h\gamma(t_{k+1})$ (7.90). Work is $O(K+\gamma(T)/\eta_q)=O(K+\varepsilon^{-3}L_\varepsilon^2)$ and storage is $O(K)$ at the chosen parameters.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - reading: error bounds at the algorithm’s parameters → for every positive constants κ and every internal accuracy 0 < ε ≤ 1; reason: the rule (6.6) is defined for every such choice and the proof uses only monotonicity of γ
--   - encoding: "Work is O(K + γ(T)/η_q) = O(K + ε^{−3}L_ε²) and storage is O(K) at the chosen parameters" → ∃ C, ε₀ > 0: for 0 < ε ≤ ε₀ the machine routine `quadProgram` (grid and quadrature, run with no matrix) halts with work ≤ C(K + γ(T)/η_q), work ≤ C(K + ε^{−3}L_ε²) and at most C·K cells touched; reason: explicit constants; the routine also computes the grid, whose O(log 1/ε) cost is within the bound
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Lemma 7.10, p. 33

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Lemma 7.10** (quadrature for `Γ_k` under Definition 2.2; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 33).
For the point quadrature (6.6) and every grid cell `[t_k, t_{k+1}]`, `0 ≤ k < K`:
`|Γ^q_k − Γ_k| ≤ η_q h/2` and `0 ≤ Γ^q_k ≤ h γ(t_{k+1})` (7.90). Work is
`O(K + γ(T)/η_q) = O(K + ε^{−3} L_ε²)` and storage is `O(K)` at the chosen parameters (the
cost of `quadProgram`, which also computes the grid, run with no matrix input). -/
theorem lemma_7_10 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (κ : AlgConsts) (hκ : κ.Pos) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k : ℕ, k < (params κ ε).K →
      |Gq (gam γ) κ ε k - Gex (gam γ) (params κ ε) k| ≤ etaq κ ε * (params κ ε).h / 2 ∧
      0 ≤ Gq (gam γ) κ ε k ∧
      Gq (gam γ) κ ε k ≤ (params κ ε).h * gam γ ((params κ ε).t (k + 1))) ∧
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ (A : Fin 0 → Fin 0 → ℝ) (ω : ℕ → ℝ), ∃ s : State,
        finalState (parisiOracles W γ) (quadProgram κ) (initState 0 A ε ω) = some s ∧
        (s.work : ℝ) ≤ C * ((params κ ε).K + gam γ (params κ ε).T / etaq κ ε) ∧
        (s.work : ℝ) ≤ C * ((params κ ε).K + ε ^ (-3 : ℤ) * Lg ε ^ 2) ∧
        (s.cells.card : ℝ) ≤ C * (params κ ε).K := by sorry

end GEGIAMP.Relative
