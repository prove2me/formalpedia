-- Prove2me | Theorems.Thm_GEGIAMP_Relative_proposition_8_4
-- name    : GEGIAMP.Relative.proposition_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:55:00.541194+00:00
-- url     : https://prove2.me/theorems/82a64781-4475-4bfc-8a53-daaf7cedb2b8
-- title:
--   Proposition 8.4 — the final query is used only in the proof; B + 1 products
-- statement:
--   Suppose $d=B+1\le N$ and fix deterministic $\omega_k>0$. Running the executed construction and the construction with the final query $q_d$ appended on the same $A$, the same leading $B\times B$ block of $J$ and the same side variables, adding independent entries $J_{rd}$ only for the final query, gives the same vector $f$ before clipping and the same rounded spin configuration. All energy estimates for the construction with $q_d$ appended therefore apply to the executed algorithm, which computes $B+1$ dense products, including rounding initialization.
--
--   Differences from the source:
--   - reading: Φ_γ is the solution of the Parisi PDE (2.3); m = Φₓ, a = Φₓₓ → Φ is `value` of the published SKFullSupport bundle (the stochastic-control formula (5.2)); m = `gradient`, a = `curvature` (Lean `deriv`), aₓ, aₓₓ further `deriv`s; reason: the paper identifies Φ with (5.2) on p. 15 (citing [AC17, Cor. 2]); Proposition 5.1 gives the spatial derivatives below time one
--   - encoding: "we fix a minimizing γ" (p. 7) and Assumption 2.1 for the Parisi diffusion (2.5) → hypothesis `Standing W γ`: IsMinimizer W γ and E[m(t,X_t)²] = t (0 ≤ t < 1) for every X with IsDiffusion W γ X (the integral form of (2.5)); reason: standing hypotheses of §§3, 7–9, written as binders
--   - encoding: the executed construction vs. the construction with q_d appended → `fvec`/`sigmaOut` with only the leading B × B block of J (`Jlead`) vs. with the full d × d J (`Jfun`); "the same probabilities" follows from the pointwise equalities; reason: in Lean both constructions are the same map; the content is that the last row and column of J are never read
--   - encoding: "the executed algorithm, which computes B + 1 dense products" → the machine run of `alg1 κ` (ω ≡ 1) halts, its output equals the construction’s rounded σ at ω ≡ 1 with J and the side variables read off its Gaussian tape (`tapeJ`, `tapeSide`), and its trace has B query products and 1 rounding product; reason: identifies the executed algorithm with the executed construction, which the source takes as its definition; the products are counted in the execution trace
--   - generalization: the input A of the algorithm is symmetric → every real N × N array A; reason: neither the construction nor the program uses symmetry; the symmetric case is an instance
--   - reading: the grid and quadrature of the algorithm → every positive constants κ and every 0 < ε ≤ 1; reason: as in Proposition 8.2
-- source:
--   Herman, Chakrabarti, Kim, Ozgul (2026), A Fully Polynomial Approximation Algorithm for the Sherrington–Kirkpatrick Model, arXiv:2611.05446v1 (version not printed; held file SHA-256 ea6508afbf5e8771a5353c9c9ce9df52a08608793fb812fc9ba947719fd5658e), Proposition 8.4, p. 44

import Mathlib
import Definitions.Def_GEGIAMP_Relative_Algorithm

open MeasureTheory ProbabilityTheory OAI.ZeroTemperatureSK
open scoped ENNReal NNReal Topology

namespace GEGIAMP.Relative

/-- **Proposition 8.4** (a final query used only in the proof; Herman, Chakrabarti, Kim, Ozgul (2026), arXiv:2611.05446v1, SHA-256 ea6508af…5658e, p. 44). Suppose
`d = B + 1 ≤ N` and fix deterministic `ω_k > 0`. The executed construction (only the leading
`B × B` block of `J`) and the construction with the final query `q_d` appended (fresh entries
`J_{rd}`), run on the same `A`, leading block and side variables, produce the same `f` and the
same rounded spins. The executed algorithm (Algorithm 1, `ω ≡ 1`, on the machine) outputs that
rounded configuration and computes `B + 1` dense products: `B` query products and one product
initializing rounding. -/
theorem proposition_8_4 {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (γ : OrderParameter) (hγ : Standing W γ) (κ : AlgConsts) (hκ : κ.Pos) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) (hdN : (params κ ε).d ≤ N) :
    let P := params κ ε
    let mo := mF W γ
    let ao := aF W γ
    let Γc := Gq (gam γ) κ ε
    (∀ (ω : ℕ → ℝ), (∀ k, 0 < ω k) → ∀ (A : Fin N → Fin N → ℝ) (J : Fin P.d → Fin P.d → ℝ)
        (η : ℕ → Fin N → ℕ → ℝ),
      fvec mo ao P Γc ω A (Jlead P.B J) η = fvec mo ao P Γc ω A (Jfun J) η ∧
      sigmaOut mo ao P Γc ω A (Jlead P.B J) η = sigmaOut mo ao P Γc ω A (Jfun J) η) ∧
    (∀ (A : Fin N → Fin N → ℝ) (tape : ℕ → ℝ), ∃ s : State,
      run (parisiOracles W γ) κ N ε A tape = some s ∧
      outVec N s = sigmaOut mo ao P Γc (fun _ => 1) A (tapeJ N P.B tape)
        (tapeSide N P.B P.mf tape) ∧
      s.marks .queryProduct = P.B ∧ s.marks .roundProduct = 1) := by sorry

end GEGIAMP.Relative
