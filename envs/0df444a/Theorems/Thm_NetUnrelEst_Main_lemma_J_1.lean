-- Prove2me | Theorems.Thm_NetUnrelEst_Main_lemma_J_1
-- name    : NetUnrelEst.Main.lemma_J_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:14:05.6412+00:00
-- url     : https://prove2.me/theorems/12b0e74e-ab0e-4770-a905-a7f1fa3e5b4f
-- title:
--   Lemma J.1 — confidence amplification of a nonnegative unbiased estimator with relative second moment C
-- statement:
--   Let $X\ge0$ with $\mathbb EX=u$ and $\mathbb EX^2\le Cu^2$ for a known $C\ge1$. For $0<\varepsilon,\delta<1$, one can form a nonnegative random variable $Y$ from $N=O(C\varepsilon^{-2}\log(2/\delta))$ independent copies of $X$ such that
--   $$\mathbb EY=u,\qquad \Pr\big(|Y-u|>\varepsilon u\big)\le\delta.$$
--   The additional scalar work is linear in the number of copies. If one copy has expected work $T$, the total expected work is $O(C\varepsilon^{-2}\log(2/\delta)(T+1))$.
--
--   This is the final step from Theorem 4.6 to Theorem 1.1. Unlike a plain median of means, the construction keeps the estimate exactly unbiased.
--
--   **Formalization Note.** There are a universal $K>0$ and one admissible program of the base randomized real RAM (the combiner). For each $(C,\varepsilon,\delta)$, a number $N\le KC\varepsilon^{-2}\log(2/\delta)$ is fixed in advance. Given the reals $C,\varepsilon,\delta,x_1,\dots,x_N$ with $x_i\ge0$, the combiner halts on every tape with work at most $KN$ and outputs $Y\ge0$. A copy is a pair $(X,\tau)$ of a value and its work on an arbitrary probability space; the two may be dependent, and $\tau$ is measurable with $T=\mathbb E\tau$. $Y$ is the combiner's output on $N$ independent copies and an independent tape. The total expected work is $\mathbb E[\sum_i\tau_i+\text{work of the combiner}]$. $\mathbb EX^2$ is a lintegral.
--
--   Differences from the source:
--   - encoding: 'form Y from O(Cε⁻² log(2/δ)) independent copies of X', 'additional scalar work linear in the number of copies' → ∃ K, ∃ one admissible combiner program of the base machine; for each C, ε, δ a count N ≤ KCε⁻² log(2/δ) fixed in advance; on every input x ≥ 0 the combiner halts on every tape with work ≤ KN and output Y ≥ 0; reason: the meaning of O(·) and of 'scalar work' on the paper's unit-cost machine; the paper fixes rk before any run
--   - encoding: a copy of X with expected work T, possibly dependent on its value → a measurable pair (X, τ) on an arbitrary probability space, T = ∫⁻ τ, copies independent under the product measure; reason: the paper's remark that the bound holds 'even when a copy's running time and returned value are dependent'
--   - encoding: EX² ≤ Cu² → ∫⁻ ofReal(X²) ≤ ofReal(Cu²); reason: avoids the junk value of a Bochner integral of a non-integrable X²; the same condition
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 62, Lemma J.1

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Machine

open scoped BigOperators ENNReal

open NetUnrelDesign.Main

namespace NetUnrelEst.Main

/-- **Lemma J.1.** There are a constant `K > 0` and one admissible program (the combiner) such
that for every known `C ≥ 1` and `0 < ε, δ < 1` there is a number `N ≤ K C ε⁻² log(2/δ)` of copies,
fixed in advance, with: given the reals `C, ε, δ, x₁, …, x_N` (`xᵢ ≥ 0`), the combiner halts on
every tape with additional scalar work at most `K N` and returns `Y ≥ 0`; and for every
nonnegative random variable `X` with `EX = u`, `EX² ≤ Cu²`, and every measurable work `τ` of a
copy (expected work `T = Eτ`), feeding `N` independent copies of `(X, τ)` to the combiner gives
`EY = u`, `Pr(|Y − u| > εu) ≤ δ`, and total expected work (copies plus combiner) at most
`K C ε⁻² log(2/δ) (T + 1)`. Sun 2027, p. 62, Lemma J.1. -/
theorem lemma_J_1 :
    ∃ K : ℝ, 0 < K ∧ ∃ P : Program, Admissible P ∧
      ∀ C ε δ : ℝ, 1 ≤ C → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∃ N : ℕ, (N : ℝ) ≤ K * C * ε⁻¹ ^ 2 * Real.log (2 / δ) ∧
          (∀ x : Fin N → ℝ, (∀ i, 0 ≤ x i) →
            OnEveryHalt P noOracleFn (initState noOracle [] ([C, ε, δ] ++ List.ofFn x))
                (fun s => 0 ≤ outReal s 0) ∧
            ∀ ω, totalWork P noOracleFn (initState noOracle [] ([C, ε, δ] ++ List.ofFn x)) ω ≤
              ENNReal.ofReal (K * N)) ∧
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
            [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℝ) (τ : Ω → ℝ≥0∞) (u : ℝ),
            Measurable X → Measurable τ → (∀ ω, 0 ≤ X ω) → MeasureTheory.Integrable X μ →
            ∫ ω, X ω ∂μ = u → ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ ≤ ENNReal.ofReal (C * u ^ 2) →
            MeasureTheory.Integrable
                (fun z : (Fin N → Ω) × ((ℕ → ℝ) × (ℕ → ℕ → ℝ)) => outReal (finalState P noOracleFn
                  (initState noOracle [] ([C, ε, δ] ++ List.ofFn fun i => X (z.1 i))) z.2) 0)
                ((MeasureTheory.Measure.pi fun _ : Fin N => μ).prod jointLaw) ∧
            ∫ z, outReal (finalState P noOracleFn
                (initState noOracle [] ([C, ε, δ] ++ List.ofFn fun i => X (z.1 i))) z.2) 0
                ∂((MeasureTheory.Measure.pi fun _ : Fin N => μ).prod jointLaw) = u ∧
            ((MeasureTheory.Measure.pi fun _ : Fin N => μ).prod jointLaw)
                {z | ¬ |outReal (finalState P noOracleFn
                  (initState noOracle [] ([C, ε, δ] ++ List.ofFn fun i => X (z.1 i))) z.2) 0 - u|
                    ≤ ε * u} ≤ ENNReal.ofReal δ ∧
            ∫⁻ z, ((∑ i, τ (z.1 i)) + totalWork P noOracleFn
                (initState noOracle [] ([C, ε, δ] ++ List.ofFn fun i => X (z.1 i))) z.2)
                ∂((MeasureTheory.Measure.pi fun _ : Fin N => μ).prod jointLaw) ≤
              ENNReal.ofReal (K * C * ε⁻¹ ^ 2 * Real.log (2 / δ)) * (∫⁻ ω, τ ω ∂μ + 1) := by sorry

end NetUnrelEst.Main
