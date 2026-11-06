-- Prove2me | Theorems.Thm_NearLinIsing_theorem_1_5
-- name    : NearLinIsing.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:52.888346+00:00
-- url     : https://prove2.me/theorems/71a70033-d25f-4d88-91c2-9037f7b4ac6c
-- title:
--   Theorem 1.5 — polymer sampling
-- statement:
--   Fix $\eta>0$ and $0<\delta<1$. Let a polymer model on a finite or countable type space have positive activities, and let $N\ge2$ be an integer such that
--
--   $$\sum_\gamma w_\gamma\le N,\qquad|X|\le N\ \text{ for every compatible family }X,\tag{2}$$
--
--   $$\sum_\gamma w_\gamma e^{\eta D(\gamma)}\le N.\tag{3}$$
--
--   Run the insertion–deletion chain from the empty family. For $0<\varepsilon<1/2$, its law after $T$ steps is within total variation distance $\varepsilon$ of $\mu$ whenever
--
--   1. $\lambda_{\min}(AW)\ge-1+\delta$ and $T\ge C_1N\log^2(N/\varepsilon)$, or
--   2. $\lambda_{\max}(AW)\le e-\delta$ and $T\ge N\exp\big(C_2\sqrt{\log(N/\varepsilon)}\big)$,
--
--   where $C_1,C_2$ depend only on $\eta$ and $\delta$. This general theorem carries the mixing of the Ising sampler and of the paper's other two applications.
--
--   Differences from the source:
--   - encoding: gives a sample within ε in the following numbers of steps → the bound is stated for every T at least the horizon; reason: total variation to a stationary law is nonincreasing in T, so the two are equivalent
--   - encoding: spectral bounds on AW → Rayleigh bounds for W^{1/2}AW^{1/2} with the diagonal, on finitely supported vectors; reason: Σw ≤ N makes this operator Hilbert–Schmidt, so the bounds are equivalent
--   - encoding: the sums in (2) and (3) → summability is assumed along with each bound; reason: a divergent `tsum` would otherwise read 0
--   - encoding: the type space (Definition 1.4, §2.4: finite or countable) → `[Countable P]`; reason: the continuously indexed extension after the theorem is a remark, not part of its statement
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Theorem 1.5, Eqs. (2)–(3), p. 4

import Mathlib
import Definitions.Def_NearLinIsing_Polymer

namespace NearLinIsing

/-- **Theorem 1.5** (Polymer sampling), p. 4, both rows of its table.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Theorem 1.5, Eqs. (2)–(3), p. 4.

Fix `η > 0` and `0 < δ < 1`. Let a polymer model on a finite or countable type space have positive
activities, and let `N ≥ 2` be an integer with `∑_γ w_γ ≤ N` and `|X| ≤ N` for every compatible
family `X` (2), and `∑_γ w_γ e^{η D(γ)} ≤ N` (3). Run the insertion–deletion chain (insert a
compatible `γ` with probability `w_γ/(4N)`, delete a present `γ` with probability `1/(4N)`, stay
otherwise) from the empty family. For `0 < ε < 1/2`, its law after `T` steps is within total
variation `ε` of `µ` whenever
1. `λmin(AW) ≥ −1 + δ` and `T ≥ C₁ N log²(N/ε)`, or
2. `λmax(AW) ≤ e − δ` and `T ≥ N exp(C₂ √log(N/ε))`,
where the constants `C₁`, `C₂` depend only on `η` and `δ`.

**Formalization Note.** Reading R7: the spectral hypotheses are Rayleigh bounds for
`W^{1/2} A W^{1/2}` with the diagonal included. Reading R8: "within ε in O(·) steps" is stated for
every `T` at least the horizon. Reading R9: countable type spaces (the continuously indexed
extension after the theorem is a remark). The sums in (2), (3) are stated with their summability. -/
theorem theorem_1_5 (η : ℝ) (hη : 0 < η) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (P : Type) [Countable P] (M : PolymerModel P) (N : ℕ), 2 ≤ N →
        (∀ γ, 0 < M.w γ) → Summable M.w → ∑' γ, M.w γ ≤ N →
        (∀ X : Finset P, M.IsCompat X → X.card ≤ N) →
        Summable (fun γ => M.w γ * Real.exp (η * M.D γ)) →
        ∑' γ, M.w γ * Real.exp (η * M.D γ) ≤ N →
        M.LambdaMinGe (-1 + δ) →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ T : ℕ, C₁ * N * Real.log (N / ε) ^ 2 ≤ T →
          tvDistC (M.stepLaw N T) M.law ≤ ε) ∧
    (∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (P : Type) [Countable P] (M : PolymerModel P) (N : ℕ), 2 ≤ N →
        (∀ γ, 0 < M.w γ) → Summable M.w → ∑' γ, M.w γ ≤ N →
        (∀ X : Finset P, M.IsCompat X → X.card ≤ N) →
        Summable (fun γ => M.w γ * Real.exp (η * M.D γ)) →
        ∑' γ, M.w γ * Real.exp (η * M.D γ) ≤ N →
        M.LambdaMaxLe (Real.exp 1 - δ) →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ T : ℕ,
          N * Real.exp (C₂ * Real.sqrt (Real.log (N / ε))) ≤ T →
          tvDistC (M.stepLaw N T) M.law ≤ ε) := by sorry

end NearLinIsing
