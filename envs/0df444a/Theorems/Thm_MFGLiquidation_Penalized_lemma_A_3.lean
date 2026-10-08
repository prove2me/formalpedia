-- Prove2me | Theorems.Thm_MFGLiquidation_Penalized_lemma_A_3
-- name    : MFGLiquidation.Penalized.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:19.984978+00:00
-- url     : https://prove2.me/theorems/435b2cde-0247-4a99-9d79-ad6eaa5412c6
-- title:
--   Lemma A.3 — the Riccati BSDEs with terminal value 2n are uniquely solvable, increase in n to A, and are bounded in ℳ_{−1} and ℳⁿ_{−1} uniformly in n
-- statement:
--   Assume Assumption 2.3 and let $(A,Z^A)$ be the solution of the singular Riccati BSDE ($A_T=+\infty$). For each integer $n\ge1$ consider
--   $$-dA^n_t=\Big(2\lambda_t-\frac{(A^n_t)^2}{2\eta_t}\Big)dt-Z^{A^n}_t\,d\widetilde W_t,\qquad A^n_T=2n. \tag{A.3}$$
--   Then:
--
--   1. for each $n\ge1$, (A.3) has a solution $(A^n,Z^{A^n})\in S^2([0,T])\times L^2([0,T];\mathbb R^m)$, and any two solutions agree ($A^n$ a.s. at every $t\le T$, $Z^{A^n}$ $dt\otimes d\mathbb P$-a.e.);
--   2. for every $n\ge1$ and $t\le T$, almost surely
--   $$A^n_t\ \ge\ \frac{1}{\frac{1}{2n}+\mathbb E\big[\int_t^T\frac{1}{2\eta_s}\,ds\,\big|\,\mathcal F_t\big]};$$
--   3. the sequence is non-decreasing: $A^n_t\le A^{n+1}_t$ a.s. for every $t\le T$;
--   4. it converges to $A$: for every $t<T$, $A^n_t\to A_t$ a.s.;
--   5. there is a constant $\mathfrak C$, independent of $n$, such that for every $n\ge1$
--   $$\|A^n\|_{\mathcal M_{-1}}+\|A^n\|_{\mathcal M^n_{-1}}\le\mathfrak C .$$
--
--   The $A^n$ are the decoupling fields of the penalized problems; the uniform bound and the monotone convergence to $A$ drive the estimates of Lemmas 4.4 and 4.5.
--
--   **Formalization Note.** Items 2–5 are stated for any family $(A^n)_{n\ge1}$ of solutions; by item 1 it is the family. The paper writes $dW_t$ in (A.3) for the $m$-dimensional $\widetilde W$ (its $Z^{A^n}$ is $\mathbb R^m$-valued). "Converges to $A$" is read pointwise in $t<T$, almost surely, as p. 25 says ("converging pointwise to $A$"). The norms are computed in $[0,\infty]$ and the constant $\mathfrak C$ is chosen before $n$. Assumption 2.3, assumed throughout the paper, implies the appendix's standing assumption ($\lambda,\eta,1/\eta$ bounded). The class $S^2\times L^2$ of $A^n$ is not printed; see the definition file.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 32, Lemma A.3; p. 25 ('converging pointwise to A')

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting
import Definitions.Def_MFGLiquidation_Penalized_Decoupled
open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Penalized

/-- Lemma A.3 (p. 32): for each `n ≥ 1` the regular Riccati BSDE (A.3) has a unique solution
`Aⁿ`, which satisfies the lower bound `Aⁿ_t ≥ 1/(1/(2n) + E[∫_t^T 1/(2η_s) ds | 𝓕_t])`; the
sequence is non-decreasing, converges pointwise to the singular solution `A`, and
`‖Aⁿ‖_{ℳ_{−1}} + ‖Aⁿ‖_{ℳⁿ_{−1}} ≤ ℭ` with `ℭ` independent of `n`. -/
theorem lemma_A_3 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Data Ω k} (hD : D.Standing P) (hA : D.Assumption23 P hD)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) (hRic : IsSingularRiccati hD A ZA) :
    (∀ n : ℕ, 1 ≤ n → ∃ (An : ℝ≥0 → Ω → ℝ) (ZAn : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      IsRegularRiccati hD n An ZAn) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ (A₁ A₂ : ℝ≥0 → Ω → ℝ) (Z₁ Z₂ : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      IsRegularRiccati hD n A₁ Z₁ → IsRegularRiccati hD n A₂ Z₂ →
      (∀ t ≤ D.T, A₁ t =ᵐ[P] A₂ t) ∧
        ∀ j, ∀ᵐ q ∂(dtP D.T P), Z₁ j q.1.toNNReal q.2 = Z₂ j q.1.toNNReal q.2) ∧
    ∀ (An : ℕ → ℝ≥0 → Ω → ℝ) (ZAn : ℕ → Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      (∀ n : ℕ, 1 ≤ n → IsRegularRiccati hD n (An n) (ZAn n)) →
      (∀ n : ℕ, 1 ≤ n → ∀ t ≤ D.T, ∀ᵐ ω ∂P,
        1 / (1 / (2 * (n : ℝ)) + P[fun ω' => ∫ s in Set.Icc (t : ℝ) D.T,
            1 / (2 * D.η s.toNNReal ω') | filtF hD t] ω) ≤ An n t ω) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t ≤ D.T, ∀ᵐ ω ∂P, An n t ω ≤ An (n + 1) t ω) ∧
      (∀ t < D.T, ∀ᵐ ω ∂P, Tendsto (fun n => An n t ω) atTop (𝓝 (A t ω))) ∧
      ∃ ℭ : ℝ≥0, ∀ n : ℕ, 1 ≤ n →
        mNorm D.T P (-1) (An n) + mnNorm D P n (-1) (An n) ≤ (ℭ : ℝ≥0∞) := by sorry

end MFGLiquidation.Penalized
