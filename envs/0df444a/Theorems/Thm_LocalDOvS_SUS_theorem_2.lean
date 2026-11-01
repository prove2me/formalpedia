-- Prove2me | Theorems.Thm_LocalDOvS_SUS_theorem_2
-- name    : LocalDOvS.SUS.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:31:22.840984+00:00
-- url     : https://prove2.me/theorems/18fc1b56-0a64-4eca-8350-b4619b212727
-- title:
--   Theorem 2, p.16 (corrected: Type-I test once per active-set size, $T_{\max} = N^2$)
-- statement:
--   Assume Assumptions 1–3: the decision space is $X=[N]$ with $N\ge2$, and $\mathcal M_C$ is the class of models with discretely convex objective $f$ and sub-Gaussian outputs with known parameter $\sigma^2$, $\sigma>0$. Let SUS be the shrinking uniform sampling algorithm (Algorithm 2), corrected so that the Type-I test is made once per active-set size and $T_{\max}=N^2$. Then:
--
--   1. for all $\epsilon>0$ and $\delta\in(0,1]$, and for every rule choosing the Type-I pair and breaking the final tie, SUS is an $[(\epsilon,\delta)\text{-PGS},\mathcal M_C]$-algorithm;
--   2. on every outcome of the simulations SUS stops after at most $25600\,\sigma^2\epsilon^{-2}\log(4N^2/\delta)+N$ simulations;
--   3. the expected simulation cost satisfies
--   $$
--   T(\epsilon,\delta,\mathcal M_C)\le\frac{102400\,\sigma^2}{\epsilon^2}\log\frac N\delta+N=O\Big[\frac1{\epsilon^2}\log\frac N\delta+N\Big];
--   $$
--   4. $T(\epsilon,\delta,\mathcal M_C)=\tilde O\big[\epsilon^{-2}\log(1/\delta)\big]$: there is $c_1>0$ such that for all $N\ge2$ and $\epsilon>0$ there is $c_2>0$ with
--   $$
--   T(\epsilon,\delta,\mathcal M_C)\le\frac{c_1}{\epsilon^2}\log\frac1\delta+c_2\qquad\text{for all }\delta\in(0,1].
--   $$
--
--   The cost does not grow with $N$ as $\delta\to0$; by the paper's lower bound (Corollary 1) the dependence on $\epsilon$ and $\delta$ is the best possible.
--
--   **Formalization Note** $T$ is an infimum over measurable deterministic sequential algorithms on $[N]$ that are $(\epsilon,\delta)$-PGS on all of $\mathcal M_C$, valued in $[0,\infty]$; an empty infimum is $\infty$. A run that never stops counts as a failure.
--
--   Differences from the source:
--   - correction: Algorithm 2 tests condition (i) after every sample (line 10) with T_max = N (line 2) → the test is made once per active-set size, when condition (ii) holds, and T_max = N²; reason: the printed claim is false: N = 3, Gaussian noise, f = (0, 2ε, 4ε), δ < 1/2 and ε small; by the law of the iterated logarithm a separation occurs before condition (ii) with probability near 1, and it is on the wrong side with probability near 1/2 (paper.md)
--   - generalization: T = O[ϵ⁻² log(N/δ) + N] with unnamed constants independent of N, d, ϵ, δ, c → T ≤ 102400σ²/ε² · log(N/δ) + N; reason: explicit constants; σ is not in §1.2's list, and 102400σ²/ε² · log(N/δ) + N ≤ max(102400σ², 1) · [ε⁻² log(N/δ) + N]
--   - generalization: expected simulation cost bound → also a sure bound on every tape (clause 2); reason: implies the expectation; p.10: the upper bounds also hold almost surely
--   - generalization: infimum over the paper's (PGS, M_C)-algorithms → infimum over measurable deterministic sequential rules on [N]; reason: a smaller class gives a larger infimum, so the bound is stronger
--   - generalization: some x, y in line 11; the point with minimal empirical mean in line 23 → every pick and tie rule; reason: contains every choice
--   - encoding: a model (X, (Y, B_Y), F) → the laws of the outputs on a product tape; reason: an algorithm sees only outputs; the product tape is the paper's independent copies
--   - encoding: ϵ ≥ 0 (p.3); σ² an upper bound on the sub-Gaussian parameter → 0 < ε and 0 < σ; reason: ε⁻² and the Hoeffding bound (division by σ²) are undefined at 0; a σ-sub-Gaussian model is σ′-sub-Gaussian for σ′ > σ
--   - encoding: the solution satisfies the guarantee with probability at least 1 − δ → outer measure of the failure set (no stop, or a bad or out-of-range point) ≤ δ; reason: the same for measurable algorithms; a run that never stops returns no solution
-- source:
--   Zhang, Zheng, Lavaei, Stochastic Localization Methods for Convex Discrete Optimization via Simulation, arXiv:2012.02427v2, Theorem 2, p.16; proof in EC.2.2, pp.ec11–ec17

import Mathlib
import Definitions.Def_LocalDOvS_SUS_sus
import Definitions.Def_LocalDOvS_SUS_simCost
import Definitions.Def_LocalDOvS_SUS_IsPGS
import Definitions.Def_LocalDOvS_SUS_InMC
import Definitions.Def_LocalDOvS_SUS_stopTime

open scoped NNReal ENNReal

namespace LocalDOvS.SUS

/-- **Theorem 2, p.16** (Zhang–Zheng–Lavaei, arXiv:2012.02427v2), for the corrected Algorithm 2.
Under Assumptions 1–3 (`X = [N]`, `N ≥ 2`, convex models with known sub-Gaussian parameter bound
`σ² > 0`):

1. for all `ε > 0`, `δ ∈ (0, 1]`, the corrected shrinking uniform sampling algorithm is an
   `[(ε, δ)-PGS, M_C]`-algorithm, for every pick and tie rule;
2. on every tape it stops after at most `25600 σ²/ε² · log(4N²/δ) + N` simulations;
3. `T(ε, δ, M_C) ≤ 102400 σ²/ε² · log(N/δ) + N`, i.e. `T(ε, δ, M_C) = O[ε⁻² log(N/δ) + N]`;
4. `T(ε, δ, M_C) = Õ[ε⁻² log(1/δ)]` in the sense of §1.2: there is `c₁ > 0` such that for all
   `N ≥ 2` and `ε > 0` there is `c₂ > 0` with `T(ε, δ, M_C) ≤ c₁ ε⁻² log(1/δ) + c₂` for every
   `δ ∈ (0, 1]`.

**Formalization Note (correction).** The printed Algorithm 2 tests condition (i) after every
sample with `T_max = N`; that version is not `(ε, δ)`-PGS (counterexample: `N = 3`, Gaussian
noise, `f = (0, 2ε, 4ε)`, small `ε`). Here the test is made once per active-set size and
`T_max = N²` (`sus`, `lookStep`, `alphaSUS`). The `O` constant is explicit and depends on `σ`
only, which §1.2 permits (σ is not among `N, d, ε, δ, c`); in clause 4, `c₁` depends on `σ`
only and `c₂` on `σ, N, ε`. `T` is `simCost`, an infimum over measurable sequential rules in
`ℝ≥0∞`. -/
theorem theorem_2 (σ : ℝ≥0) (hσ : 0 < σ) :
    (∀ N : ℕ, 2 ≤ N → ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 →
      (∀ M : Model, InMC N σ M →
        ∀ (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool),
          IsPGS N ε δ (sus N σ ε δ pick tie) M) ∧
      (∀ (pick : SUSState → (ℕ → ℕ → ℝ) → ℕ × ℕ) (tie : SUSState → (ℕ → ℕ → ℝ) → Bool)
          (ω : ℕ × ℕ → ℝ),
        stopTime (sus N σ ε δ pick tie) ω ≠ ⊤ ∧
          ((stopTime (sus N σ ε δ pick tie) ω).toNat : ℝ) ≤
            25600 * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (4 * (N : ℝ) ^ 2 / δ) + N) ∧
      simCost N σ ε δ ≤
        ENNReal.ofReal (102400 * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (N / δ) + N)) ∧
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ N : ℕ, 2 ≤ N → ∀ ε : ℝ, 0 < ε → ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        simCost N σ ε δ ≤ ENNReal.ofReal (c₁ / ε ^ 2 * Real.log (1 / δ) + c₂) := by sorry

end LocalDOvS.SUS
