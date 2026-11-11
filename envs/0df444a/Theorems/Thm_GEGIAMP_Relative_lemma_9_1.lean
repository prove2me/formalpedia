-- Prove2me | Theorems.Thm_GEGIAMP_Relative_lemma_9_1
-- name    : GEGIAMP.Relative.lemma_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:54:47.98791+00:00
-- url     : https://prove2.me/theorems/e9a0cacb-a068-496b-ad56-a3c9d0da93f1
-- title:
--   Lemma 9.1 — energy estimates for GEG-IAMP
-- statement:
--   There are universal $K,\varepsilon_0>0$ and fixed algorithmic constants such that for $0<\varepsilon\le\varepsilon_0$ and $0<\alpha<1/2$, if $N\ge K\varepsilon^{-2}L_\varepsilon^2L_\alpha$ (9.1), then with probability at least $1-\alpha$ the output $\sigma$ of Algorithm 1 at internal additive accuracy per spin $\varepsilon$ and the optimum satisfy $H_N(\sigma)\ge(P^*-\varepsilon/2)N$ and $\mathrm{OPT}_N\le(P^*+\varepsilon/2)N$ (9.2); in particular $0\le\mathrm{OPT}_N-H_N(\sigma)\le\varepsilon N$ on this event. Before simplification its work is $O\{N^2B+NB^2+NK+K+\varepsilon^{-3}L_\varepsilon^2+N^2\}$ (9.3), where $B=\Theta(\varepsilon^{-1})$ and $K=\Theta(\varepsilon^{-2}L_\varepsilon^2)$; under (9.1) the work is $O(N^2/\varepsilon)$, there are $B+1$ executed dense products and storage is $O(N^2)$.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - encoding: Algorithm 1 with fixed algorithmic constants under Definition 2.2 → the machine program `alg1 κ` with ∃ κ (positive constants), run with the Parisi oracles; reason: one concrete program; constants existentially quantified as printed
--   - encoding: K, Θ and O with universal constants; L_α = log(K/α) → one explicit C > 0 in (9.1), in L_α = log(C/α) and in every bound; reason: explicit constants
--   - encoding: "with probability at least 1 − α" jointly over A and the algorithm → outer measure ≤ α of the failure set under GOE(N) ⊗ i.i.d. N(0,1) tape; the success event also requires the run to halt with a spin vector; reason: failure form, no measurability side condition
--   - encoding: work, storage and product counts → on every run with symmetric A and every tape: work (unit operations, memory accesses included) ≤ C·(9.3) and ≤ C N²/ε, B query products and one rounding product in the trace, cells touched (input included) ≤ C N²; reason: worst case, from the machine semantics
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Lemma 9.1, p. 60

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Lemma 9.1** (energy estimates for GEG-IAMP; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 60). There are universal
`K, ε₀ > 0` and fixed algorithmic constants such that for `0 < ε ≤ ε₀`, `0 < α < 1/2` and
`N ≥ K ε^{−2} L_ε² L_α` (9.1), `L_α = log(K/α)`: with probability at least `1 − α` (joint over
`A ∼ GOE(N)` and the algorithm's Gaussian draws) the output `σ` of Algorithm 1 at internal
additive accuracy `ε` and the optimum satisfy `H_N(σ) ≥ (P* − ε/2)N`, `OPT_N ≤ (P* + ε/2)N`
(9.2). Its work is `O{N²B + NB² + NK + K + ε^{−3}L_ε² + N²}` (9.3) with `B = Θ(ε^{−1})`,
`K = Θ(ε^{−2}L_ε²)`; under (9.1) the work is `O(N²/ε)`, there are `B + 1` executed dense
products and the storage is `O(N²)`. -/
theorem lemma_9_1 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) :
    ∃ κ : AlgConsts, κ.Pos ∧ ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε α : ℝ, 0 < ε → ε ≤ ε₀ → 0 < α → α < 1 / 2 →
      let P := params κ ε
      -- B = Θ(1/ε), K = Θ(ε⁻² L_ε²)  (6.4)
      (C⁻¹ / ε ≤ P.B ∧ (P.B : ℝ) ≤ C / ε ∧
        C⁻¹ * ε ^ (-2 : ℤ) * Lg ε ^ 2 ≤ P.K ∧ (P.K : ℝ) ≤ C * ε ^ (-2 : ℤ) * Lg ε ^ 2) ∧
      ∀ N : ℕ, C * ε ^ (-2 : ℤ) * Lg ε ^ 2 * Real.log (C / α) ≤ N →
        -- (9.2) with probability at least 1 − α
        jointLaw N {p | ¬ ∃ s : State, run (parisiOracles W γ) κ N ε p.1 p.2 = some s ∧
            IsSpin (outVec N s) ∧
            (Pstar W γ - ε / 2) * N ≤ H p.1 (outVec N s) ∧
            OPT p.1 ≤ (Pstar W γ + ε / 2) * N ∧
            -- in particular 0 ≤ OPT_N − H_N(σ) ≤ εN on this event
            0 ≤ OPT p.1 - H p.1 (outVec N s) ∧ OPT p.1 - H p.1 (outVec N s) ≤ ε * N} ≤
          ENNReal.ofReal α ∧
        -- work (9.3), O(N²/ε), B + 1 products, storage O(N²): on every run
        ∀ (A : Fin N → Fin N → ℝ), IsSymm A → ∀ tape : ℕ → ℝ, ∃ s : State,
          run (parisiOracles W γ) κ N ε A tape = some s ∧
          (s.work : ℝ) ≤ C * ((N : ℝ) ^ 2 * P.B + N * (P.B : ℝ) ^ 2 + N * P.K + P.K +
            ε ^ (-3 : ℤ) * Lg ε ^ 2 + (N : ℝ) ^ 2) ∧
          (s.work : ℝ) ≤ C * N ^ 2 / ε ∧
          s.marks .queryProduct = P.B ∧ s.marks .roundProduct = 1 ∧
          (s.cells.card : ℝ) ≤ C * N ^ 2 := by sorry

end GEGIAMP.Relative
