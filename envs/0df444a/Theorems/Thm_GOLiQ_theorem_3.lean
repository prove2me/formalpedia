-- Prove2me | Theorems.Thm_GOLiQ_theorem_3
-- name    : GOLiQ.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:20.458364+00:00
-- url     : https://prove2.me/theorems/afa477e7-02d8-4c52-a36e-a6885add2a26
-- title:
--   Theorem 3 — GOLiQ: bias $\le K_0/(8k)$, step variance $O(1/k)$, and regret $O((\log M_L)^2)$
-- statement:
--   Suppose Assumptions 1 to 3 hold, and let GOLiQ (Algorithm 1) run with warm-up parameter $\xi\in(0,1)$, initial value $x_1\in\mathcal B$, and
--   $$\eta_k=c_\eta/k\ \text{ with } c_\eta\ge 2/K_0,\tag{20}$$
--   $$D_k=a_D+b_D\log k\ \text{ with } a_D\ge\frac{C_D}{\min(\gamma,\eta)\xi}\ \text{ and } b_D\ge\frac{8}{\min(\gamma,\eta)\xi},\tag{21}$$
--   where $C_D$ is the constant of (36). Then
--
--   1. there is $K_3>0$ such that $B_k\le\dfrac{K_0}{8k}$ and $\eta_k\mathcal V_k\le\dfrac{K_3}{k}$ for all $k\ge1$;
--   2. there is $K_2>0$ such that $\mathbb E[\|x_k-x_{k+1}\|^2]\le K_2k^{-2}$ for all $k\ge1$;
--   3. there is $K_{alg}$ such that the regret satisfies
--   $$R(L)\le K_{alg}\,(\log M_L)^2=O((\log M_L)^2)\quad\text{for all }L\ge1,\tag{23}$$
--   where $M_L=\sum_{k=1}^LD_k$ is the number of customers served by cycle $L$.
--
--   The regret against the optimal steady-state cost thus grows only logarithmically (squared) in the number of customers served.
--
--   Differences from the source:
--   - encoding: fee p > 0, service and arrival rates, the box [µ̲, µ̄] × [p̲, p̄] → 0 < µ̲ < µ̄, 0 < p̲ < p̄ and 0 < λ(p̄); reason: the fee is p > 0 (p.10) and rates are positive; λ′, c′ and ∇f on B are determined only when the intervals are nondegenerate
--   - encoding: λ and c continuously differentiable, with derivatives λ′ and c′ → C¹ on the closed intervals [p̲, p̄] and [µ̲, µ̄], λ′ and c′ the derivatives within them; reason: only values on the box enter the model
--   - encoding: U and V independent i.i.d. sequences with unit means; Z drawn in Algorithm 1 → nonnegative Uₙ, Vₙ and the draws Zₖ (uniform on {1, 2}) on one probability space, all mutually independent; reason: Uₙ/λ and Vₙ/µ are times; statements that do not mention Z do not depend on it
--   - encoding: x = (µ, p) with the Euclidean norm → a point of EuclideanSpace ℝ (Fin 2), coordinate 0 = µ, 1 = p; reason: the norm of p.12
--   - encoding: ∇f in Assumption 3 and x* = (µ*, p*) optimal → a field g with HasGradientWithinAt f (g x) B x for x ∈ B, and x* ∈ B a minimizer of f on B; reason: Lemma 5 gives differentiability; Assumption 3(a) already forces x* to be the minimizer
--   - reading: a sufficiently small constant η > 0 (Assumption 2) → there is η₀ > 0, depending only on the model and the laws of U and V, such that the statement holds for every η ≤ η₀ that satisfies Assumption 2; reason: with η fixed the statement is false: U, V ~ Exp(1), λ(p̲) = 0.99, µ̲ = 1, µ̄ = 2, η = 0.5, θ = 0.005, a = 0.004, γ = 5·10⁻⁶ satisfy Assumption 2, yet under the constant policy (µ̲, p̲) E[exp(ηWₙ)] → E[exp(ηW∞)] = ∞; the proof of Lemma 1 (p.54) needs η below the decay rate η̄ of the dominating queue
--   - reading: the per-cycle indexing of §3.3 with leftovers, recursions (6)–(7) and the price rule of p.15 → one global customer index j = N_{k−1} + n; customer 0 arrives at time 0 to an empty system; customer j pays p_{c(j−1)}, c(i) the last cycle that started strictly before the arrival of customer i; reason: it reproduces (6)–(7) with W₀¹ = 0, Q₁ = 0, and charges the first new arrival of cycle k the old fee p_{k−1}
--   - reading: 𝓕ₖ, the σ-algebra including all events in the first k − 1 iterations → 𝓕ₖ = σ(Uⱼ, Vⱼ : j ≤ N_{k−1}; Z₁, …, Z_{k−1}); an admissible policy has each xₖ ∈ B and 𝓕ₖ-measurable; reason: the primitives of every customer who entered service in cycles 1, …, k − 1 and the coordinate draws (p.68: xₖ ∈ 𝓕ₖ)
--   - encoding: W∞(µ, p), the steady-state waiting time → Loynes' supremum sup_{n≥0} Σ_{j=1}^n (Vⱼ/µ − Uⱼ/λ(p)) on the primitives; reason: it has the stationary law; it is the coupling from the past of p.58
--   - encoding: Π_B, the projection onto B → the coordinatewise clamp to [µ̲, µ̄] × [p̲, p̄]; reason: the Euclidean projection onto a box
--   - reading: Dₖ = a_D + b_D log(k) → Dₖ = ⌈a_D + b_D log k⌉ with the natural logarithm; reason: Dₖ counts customers; the ceiling is the smallest admissible integer
--   - reading: Hₖ ← (2h, 0) for the p-partial when Z = 1 and (0, 2h) for the µ-partial, with x = (µ, p) → each partial in its own coordinate: (0, 2ĝ_p) if Zₖ = 1, (2ĝ_µ, 0) if Zₖ = 2; reason: the proof of (i) (p.68) pairs h¹ₖ with ∂f/∂p and h²ₖ with ∂f/∂µ; the literal swap would make E[Hₖ | 𝓕ₖ] estimate (∂_p f, ∂_µ f) and Bₖ ≤ K₀/(8k) fail
--   - reading: Algorithm 1's loop 'for n = 1, …, Dₖ', λ(p)/µₖ and the proof's 1/µ → the loop over cycles k, λ(pₖ)/µₖ and 1/µₖ; reason: typos: the input line names L, and the proof (p.68) writes λ(pₖ)
--   - reading: C_D with the explicit formula (36) → ∃ C_D chosen after the model and ξ, uniform in a_D, b_D, c_η and x₁; reason: (36) builds C_D from constants A, M, K₄ that the paper only asserts to exist
--   - reading: log(M_L)² → (log M_L)²; reason: Remark 9(iii) ('the square in log(M_L)²') and p.71 ('log(L)² ≤ log(M_L)²')
--   - generalization: (iii) → also asserts integrability of each cycle cost and each Tₖ, k ≤ L; reason: implied by Lemma 1; it excludes junk values in R(L)
--   - encoding: expectations of nonnegative quantities → lower Lebesgue integrals in [0, ∞]; reason: a finite bound then also asserts finiteness, and no junk value 0 arises for a non-integrable quantity
--   - encoding: f of (2), through the steady-state queue length Q∞(µ, p) → f defined by (5), h₀λ(p)(E[W∞(µ, p)] + 1/µ) + c(µ) − pλ(p); reason: the paper's own identity (5) (Little's law, p.13) for every (µ, p) ∈ B; Q∞ is not used elsewhere
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, Theorem 3, p.33; (20), p.32; (21), p.33; (36), p.70; Algorithm 1, p.32

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives
import Definitions.Def_GOLiQ_Assumption2
import Definitions.Def_GOLiQ_Model_objective
import Definitions.Def_GOLiQ_Assumption3
import Definitions.Def_GOLiQ_CycleSystem
import Definitions.Def_GOLiQ_Primitives_info
import Definitions.Def_GOLiQ_Model_regret
import Definitions.Def_GOLiQ_estimatorBias
import Definitions.Def_GOLiQ_estimatorVariance
import Definitions.Def_GOLiQ_Model_goliq

open MeasureTheory

namespace GOLiQ

/-- **Theorem 3 (regret bound for Algorithm 1)** (Chen, Liu, Hong, arXiv:2009.02911v3, p.33):
suppose Assumptions 1 to 3 hold, and `ηₖ` and `Dₖ` are selected according to

`ηₖ = c_η/k` with `c_η ≥ 2/K₀`,    (20)
`Dₖ = a_D + b_D log(k)` with `a_D ≥ C_D/(min(γ, η)ξ)` and `b_D ≥ 8/(min(γ, η)ξ)`,    (21)

for any warm-up parameter `ξ ∈ (0, 1)`. Then

(i) there is `K₃ > 0` such that `Bₖ ≤ K₀/(8k)` and `ηₖ𝒱ₖ ≤ K₃/k`;
(ii) there is `K₂ > 0` such that `E[‖xₖ − xₖ₊₁‖²] ≤ K₂k^{−2}`;    (22)
(iii) the regret of Algorithm 1 satisfies `R(L) ≤ K_alg log(M_L)² = O(log(M_L)²)`,    (23)

where `M_L = Σ_{k=1}^L Dₖ` is the number of customers served by cycle `L`.

**Formalization Note.**
* `xₖ` and `Hₖ` are the iterates and estimators of GOLiQ (`Model.goliq`, `Model.goliqEstimator`),
  run from any `x₁ ∈ B`; the queue is the cycle system of §3.3 under these iterates; `Bₖ`, `𝒱ₖ` are
  (4) with `𝓕ₖ = σ(Uⱼ, Vⱼ, j ≤ Nₖ₋₁; Z₁, …, Zₖ₋₁)` and `∇f` the gradient field `g` of Assumption 3.
* `Dₖ = ⌈a_D + b_D log k⌉` (customers are counted by integers; natural logarithm).
* `C_D` ((36), p.70) is built from constants that the paper only asserts to exist; it is
  existential here, chosen after the model and `ξ`, and uniform in `a_D, b_D, c_η, x₁`. `K₃, K₂, K_alg`
  are chosen after `a_D, b_D, c_η, x₁` and are uniform in `k` and `L`.
* "Sufficiently small `η`" (Assumption 2) is read as: for all `η` below a threshold `η₀` that depends
  only on the model and the laws of `U, V`.
* `log(M_L)²` is `(log M_L)²` (Remark 9(iii) and p.71). `R(L)` is (9). Part (iii) also asserts that
  each cycle cost of (8) and each `Tₖ` is integrable, so that `R(L)` is a genuine expectation.
  `Bₖ`, `𝒱ₖ` and `E‖·‖²` are lower Lebesgue integrals in `[0, ∞]`, so (i) and (ii) assert finiteness. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η θ a γ : ℝ, Assumption2 M Pr η θ a γ → η ≤ η₀ →
    ∀ (g : Point → Point) (xstar : Point) (K₀ K₁ : ℝ), Assumption3 M Pr g xstar K₀ K₁ →
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 →
    ∃ C_D : ℝ, ∀ a_D b_D c_η : ℝ,
      C_D / (min γ η * ξ) ≤ a_D → 8 / (min γ η * ξ) ≤ b_D → 2 / K₀ ≤ c_η →
    ∀ x₁ : Point, x₁ ∈ M.box →
      let D : ℕ → ℕ := fun k => ⌈a_D + b_D * Real.log k⌉₊
      let step : ℕ → ℝ := fun k => c_η / k
      let x := M.goliq Pr ξ D step x₁
      let H := M.goliqEstimator Pr ξ D step x₁
      (∃ K₃ : ℝ, 0 < K₃ ∧ ∀ k : ℕ, 1 ≤ k →
          estimatorBias Pr (Pr.info D) g x H k ≤ ENNReal.ofReal (K₀ / (8 * k)) ∧
          ENNReal.ofReal (step k) * estimatorVariance Pr H k ≤ ENNReal.ofReal (K₃ / k)) ∧
      (∃ K₂ : ℝ, 0 < K₂ ∧ ∀ k : ℕ, 1 ≤ k →
          ∫⁻ ω, ‖x k ω - x (k + 1) ω‖ₑ ^ 2 ∂Pr.P ≤ ENNReal.ofReal (K₂ * (k : ℝ) ^ (-2 : ℤ))) ∧
      (∃ K_alg : ℝ, ∀ L : ℕ, 1 ≤ L →
          (∀ k : ℕ, 1 ≤ k → k ≤ L →
            Integrable (fun ω => (M.system Pr D x ω).cost k) Pr.P ∧
            Integrable (fun ω => (M.system Pr D x ω).length k) Pr.P) ∧
          M.regret Pr D x xstar L ≤
            K_alg * Real.log (∑ k ∈ Finset.Icc 1 L, (D k : ℝ)) ^ 2) := by sorry

end GOLiQ
