-- Prove2me | Theorems.Thm_GEGIAMP_Relative_theorem_3_1
-- name    : GEGIAMP.Relative.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:54:48.592603+00:00
-- url     : https://prove2.me/theorems/c2cf23f9-8afd-433b-bfe8-e54434eedf79
-- title:
--   Theorem 3.1 — relative approximation by GEG-IAMP
-- statement:
--   Under Assumption 2.1 and Definition 2.2 there are constants $c,\mathsf K>0$ (after the fixed algorithmic constants) such that for $0<\varepsilon\le1$ and $0<\alpha<1/2$, with $\eta_{\rm acc}=c\varepsilon$ and $N_0=\lceil\mathsf K\eta_{\rm acc}^{-2}L^2_{\eta_{\rm acc}}L_\alpha\rceil$, $L_\alpha=\log(\mathsf K/\alpha)$: for every $N\ge N_0$, Algorithm 1 at internal accuracy $\eta_{\rm acc}$ returns $\sigma\in\{-1,1\}^N$ with $\mathbb P\{H_N(\sigma)\ge(1-\varepsilon)\mathrm{OPT}_N\}\ge1-\alpha$ (3.3), jointly over $A\sim$ GOE$(N)$ and the algorithm's Gaussian draws. Total work is at most $\mathsf KN^2/\varepsilon$ and storage is $O(N^2)$. The algorithm uses $K=\Theta(\varepsilon^{-2}L_\varepsilon^2)$ discretization steps grouped into $B=\Theta(\varepsilon^{-1})$ observation intervals, and executes $B$ matrix queries and one further dense product to initialize rounding, $B+1$ products in total. Before simplification the total work is $O(N^2B+NB^2+NK+K+\varepsilon^{-3}L_\varepsilon^2+N^2)$ (3.4).
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - encoding: Algorithm 1 under Definition 2.2, with fixed algorithmic constants → the machine program `alg1 κ` (Appendix A line by line) with ∃ κ positive before c, 𝖪, run with the Parisi oracles γ, m, a; reason: one concrete costed program; constants existentially quantified as printed
--   - encoding: universal 𝖪, Θ and O(·) → one explicit C > 0 used in N₀, in L_α = log(C/α), in the work bound C N²/ε and in every Θ/O clause; reason: explicit constants
--   - encoding: P{H_N(σ) ≥ (1 − ε) OPT_N} ≥ 1 − α, joint over A and the algorithm’s randomness → outer measure ≤ α of the failure set under GOE(N) ⊗ i.i.d. N(0,1) tape; success also requires the run to halt with σ ∈ {−1,1}^N; reason: failure form, no measurability side condition
--   - encoding: work, storage, steps and products → on every run with symmetric A and every tape: work (unit operations, memory accesses charged) ≤ C N²/ε and ≤ C·(3.4); cells touched (input included) ≤ C N²; N·K executed Euler–Maruyama step blocks (K per coordinate); B query products and one rounding product in the trace; K, B at η_acc bounded above and below by C^{±1} ε^{−2}L_ε² and C^{±1}/ε; reason: worst case, read off the machine semantics
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Theorem 3.1, p. 8

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Theorem 3.1** (relative approximation by GEG-IAMP; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 8). Under
Assumption 2.1 and Definition 2.2 there are (fixed algorithmic constants and) constants
`c, K > 0` such that for `0 < ε ≤ 1` and `0 < α < 1/2`, with `η_acc = cε` and
`N₀ = ⌈K η_acc^{−2} L²_{η_acc} L_α⌉`, `L_α = log(K/α)`: for every `N ≥ N₀`, Algorithm 1 at internal
accuracy `η_acc` returns `σ ∈ {−1, 1}^N` with `P{H_N(σ) ≥ (1 − ε) OPT_N} ≥ 1 − α` (joint over
`A ∼ GOE(N)` and the algorithm's Gaussian draws); total work is at most `K N²/ε` and storage
`O(N²)`; it uses `K = Θ(ε^{−2} L_ε²)` discretization steps grouped into `B = Θ(ε^{−1})`
observation intervals, and executes `B` matrix queries and one further dense product to
initialize rounding, `B + 1` products in total; before simplification the work is
`O(N²B + NB² + NK + K + ε^{−3}L_ε² + N²)` (3.4). -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) :
    ∃ κ : AlgConsts, κ.Pos ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ε α : ℝ, 0 < ε → ε ≤ 1 → 0 < α → α < 1 / 2 →
      let η := c * ε
      let P := params κ η
      -- K = Θ(ε⁻² L_ε²) steps in B = Θ(1/ε) groups
      (C⁻¹ * ε ^ (-2 : ℤ) * Lg ε ^ 2 ≤ P.K ∧ (P.K : ℝ) ≤ C * ε ^ (-2 : ℤ) * Lg ε ^ 2 ∧
        C⁻¹ / ε ≤ P.B ∧ (P.B : ℝ) ≤ C / ε) ∧
      ∀ N : ℕ, ⌈C * η ^ (-2 : ℤ) * Lg η ^ 2 * Real.log (C / α)⌉₊ ≤ N →
        -- (3.3), in failure form
        jointLaw N {p | ¬ ∃ s : State, run (parisiOracles W γ) κ N η p.1 p.2 = some s ∧
            IsSpin (outVec N s) ∧ (1 - ε) * OPT p.1 ≤ H p.1 (outVec N s)} ≤ ENNReal.ofReal α ∧
        -- work, storage, products and steps: on every run
        ∀ (A : Fin N → Fin N → ℝ), IsSymm A → ∀ tape : ℕ → ℝ, ∃ s : State,
          run (parisiOracles W γ) κ N η A tape = some s ∧
          IsSpin (outVec N s) ∧
          (s.work : ℝ) ≤ C * N ^ 2 / ε ∧
          (s.cells.card : ℝ) ≤ C * N ^ 2 ∧
          s.marks .step = N * P.K ∧
          s.marks .queryProduct = P.B ∧ s.marks .roundProduct = 1 ∧
          -- (3.4)
          (s.work : ℝ) ≤ C * ((N : ℝ) ^ 2 * P.B + N * (P.B : ℝ) ^ 2 + N * P.K + P.K +
            ε ^ (-3 : ℤ) * Lg ε ^ 2 + (N : ℝ) ^ 2) := by sorry

end GEGIAMP.Relative
