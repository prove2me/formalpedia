-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_theorem_1_1
-- name    : IteratedLP.Gaussian.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:22:12.228657+00:00
-- url     : https://prove2.me/theorems/779a255f-e5f8-4ab8-8ccc-cb22f8e4242e
-- title:
--   Theorem 1.1 — Gaussian state evolution: ITERATED-LP's empirical laws converge in $W_2$ and $|B_t|/N\to1-q_t$
-- statement:
--   Let $\alpha>0$, let $K\ge1$, and let $\kappa_1>\dots>\kappa_K$ be margins such that $(\alpha,\kappa_1)$ satisfies the first-round feasibility condition (1.2). For each $N$ let $M=\lfloor\alpha N\rfloor$, $A_{ij}$ i.i.d. $N(0,1/N)$ and $v_1,\dots,v_K$ i.i.d. $N(0,I_N)$ independent of $A$, and run ITERATED-LP (Algorithm 1) with frozen sets $B_t$ and empirical trajectory laws $\hat\mu^{\mathrm{col}}_{N,t}$, $\hat\mu^{\mathrm{row}}_{N,t}$. Let $q_t$, $\mu^{\mathrm{col}}_t$ and $\mu^{\mathrm{row}}_t$ be given by the state-evolution recursion (Algorithm 2). Then, jointly for $1\le t\le K$,
--   $$W_2\big(\hat\mu^{\mathrm{col}}_{N,t},\mu^{\mathrm{col}}_t\big)\xrightarrow{\ \mathbb P\ }0,\qquad W_2\big(\hat\mu^{\mathrm{row}}_{N,t},\mu^{\mathrm{row}}_t\big)\xrightarrow{\ \mathbb P\ }0,\qquad \frac{|B_t|}N\xrightarrow{\ \mathbb P\ }1-q_t.$$
--   Precisely: Algorithm 2 admits a state-evolution sequence, and for every such sequence and every $\varepsilon>0$, the probability that ITERATED-LP is undefined, or that for some choice of LP optimizers and some $t\le K$ one of the three quantities deviates from its limit by more than $\varepsilon$, tends to $0$ as $N\to\infty$.
--
--   The theorem describes, in every round, how many coordinates have frozen to signs, how the remaining coordinates are distributed and how much slack the row constraints retain; the paper's algorithm for the binary perceptron (Theorem 1.3) is built on it.
--
--   Differences from the source:
--
--   - reading: let x^(t) be an optimal solution (Algorithm 1) → the failure event counts every run, i.e. every choice of optimizers in every round, and its probability is the outer measure; reason: the event 'some run fails' contains the failure event of each selection of optimizers, so this implies the theorem for every selection; it is the stronger reading
--   - reading: jointly for 1 ≤ t ≤ K, W₂(…) →P 0, W₂(…) →P 0, |B_t|/N →P 1 − q_t → for every ε > 0, P(ITERATED-LP undefined, or some run and some t ≤ K with W₂(μ̂^col_{N,t}, μ^col_t) > ε or W₂(μ̂^row_{N,t}, μ^row_t) > ε or ||B_t|/N − (1 − q_t)| > ε) → 0; reason: the quantities exist only when the LPs are feasible; counting an undefined run as a failure is the stronger reading (the paper's proof shows ITERATED-LP is defined with high probability)
--   - reading: q_t, μ^col_t, μ^row_t given by the state-evolution recursion (Algorithm 2), which takes 'the maximizer', a dual minimizer and 'the multiplier' → IsStateEvolution α K κ S as a relation (each round is the output of some valid choice); conclusion: a state-evolution sequence exists, and every sequence satisfying the relation has the convergences, with μ^row_t the first marginal of π^row_t; reason: the paper proves that the choices exist and that ω⋆_t is unique; the ∃/∀ form is the full-strength reading and the recursion is computed, not assumed
--   - encoding: suprema and minima in which Y (resp. Ũ) may depend on the state, the fresh Gaussians and independent randomness → suprema and infima over joint laws (couplings) with the prescribed marginal; the row set requires Ũ ∈ L²; reason: same values: extra randomization does not lower the row minimum (conditional expectation), and the minimum is attained
--   - encoding: first-round feasibility condition (1.2) with a supremum over ρ ∈ (0, 1] → FirstRoundFeasible: ∃ ρ ∈ (0, 1] with α E(κ₁ − ρG)₊² < φ₁(ρ)², φ₁ a supremum over joint laws of (G, Y); reason: equivalent (positive denominator), and correct when the supremum is +∞
--   - encoding: W₂ with respect to the Euclidean norm on ℝ^t → W2 = (transportCost with cost ‖x − y‖² on EuclideanSpace ℝ (Fin t))^{1/2} in [0, ∞]; reason: §1.6
--   - encoding: M = ⌊αN⌋, which is 0 for finitely many N → for M = 0 the row empirical law is the zero measure, its W₂ distance to a probability law is ∞, and the failure event holds; reason: affects finitely many N only (α > 0), so the limit is unchanged
--   - encoding: rounds 1, …, K; empty histories at t = 1 with the omitted terms of (6.18), (6.24), (6.25) and §4.2 → 0-based κ : Fin K → ℝ and runs; trajectories in RVec t for 1 ≤ t ≤ K; the empty state of RVec 0 Dirac laws; lastE, lastV, lastDiag, lastCol vanish at p = 0 and the frozen term of μ^col_t is dropped at p = 0; reason: relabelling and the paper's conventions
--   - encoding: (Q^x)⁻¹, (Q^λ)⁻¹ in Steps 3 and 5 → Mathlib's matrix inverse (0 for a singular matrix); reason: the paper proves Q^x, Q^λ ≻ 0 along the recursion (Theorem 7.6), so the junk value never occurs
--   - encoding: the probability space for each N → modelLaw = (A_ij i.i.d. N(0, 1/N)) ⊗ (v_t i.i.d. N(0, I_N)) on (Fin M → Fin N → ℝ) × (Fin K → Fin N → ℝ); K ≥ 1 so that κ₁ exists; reason: Algorithm 1 and Theorem 1.1
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, pp. 4–5, Theorem 1.1 (proved on p. 40)

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_Model
import Definitions.Def_IteratedLP_Gaussian_Feasibility
import Definitions.Def_IteratedLP_Gaussian_StateEvolution

open MeasureTheory ProbabilityTheory Filter Topology

namespace IteratedLP.Gaussian

/-- Theorem 1.1 (Gaussian state evolution, pp. 4–5). Let `α > 0`, `K ≥ 1`, margins
`κ_1 > ⋯ > κ_K` with `(α, κ_1)` satisfying (1.2), `M = ⌊αN⌋`, `A_ij` i.i.d. `N(0, 1/N)` and
`v_1, …, v_K` i.i.d. `N(0, I_N)` independent of `A`. Algorithm 2 admits a state-evolution
sequence, and for every such sequence and every `ε > 0`, the probability that ITERATED-LP is
undefined, or that some choice of LP optimizers and some round `1 ≤ t ≤ K` has
`W₂(μ̂^col_{N,t}, μ^col_t) > ε`, `W₂(μ̂^row_{N,t}, μ^row_t) > ε` or `||B_t|/N - (1 - q_t)| > ε`,
tends to `0` as `N → ∞` (outer measure). -/
theorem theorem_1_1 (α : ℝ) (hα : 0 < α) (K : ℕ) (hK : 0 < K) (κ : Fin K → ℝ)
    (hκ : StrictAnti κ) (h12 : FirstRoundFeasible α (κ ⟨0, hK⟩)) :
    (∃ S : (p : ℕ) → PopState p, IsStateEvolution α K κ S) ∧
    ∀ S : (p : ℕ) → PopState p, IsStateEvolution α K κ S → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N : ℕ => modelLaw (numRows α N) N K
        (deviationEvent α K κ (fun t => (S t).q) (fun t => (S t).μcol)
          (fun t => (S t).πrow.map Prod.fst) ε N)) atTop (𝓝 0) := by sorry

end IteratedLP.Gaussian
