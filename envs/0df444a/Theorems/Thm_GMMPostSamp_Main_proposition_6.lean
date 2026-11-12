-- Prove2me | Theorems.Thm_GMMPostSamp_Main_proposition_6
-- name    : GMMPostSamp.Main.proposition_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:28:51.299272+00:00
-- url     : https://prove2.me/theorems/a580a7e0-fc85-4646-b439-6b7bd87c3b10
-- title:
--   Proposition 6 — small noise σ² ≤ 1/(C log(n/δ)): two LearnGMM calls and a matching-law relabelling solve Problem 1
-- statement:
--   There are an admissible program and a universal $C>0$ such that for all $k,d,n\ge1$, $\sigma>0$, $0<a\le A$, $\alpha\in[a,A]^k$ and $\delta\in(0,\frac16)$, with $\tau$ as in Proposition 4 at $\delta^2/24$, i.e. $\tau=\frac1{Ak}(\frac{\delta^2/24}{8k})^{1/a}$, and $r=\frac1{16}$: if
--   $$d\ge C\Big(k+\log\frac1\delta\Big),\qquad\sigma^2\le\frac1{C\log(n/\delta)},\qquad n\ge C\frac{d^3k^{11}(1+\sigma^8)}{\tau^6r^2},$$
--   then the program solves Problem 1, and on every input $x_{[n]}$ every run halts within $C(nd^2+nk^3)+C(ndk+k^4\log^7(k/\delta))+C$ steps — two LearnGMM calls plus $O(ndk+k^4\log^7(k/\delta))$ additional time. It handles the high signal-to-noise branch of Theorem 3.
--
--   Differences from the source:
--   - reading: n ≥ C(d³k¹¹(1+σ⁸)/(τ⁶r²)) with r not fixed in the statement → r = 1/16; reason: the proof runs LearnGMM with r ← 1/16 (p. 25)
--   - reading: an algorithm that solves Problem 1 using two calls to LearnGMM in Proposition 4, and O(ndk + k⁴log⁷(k/δ)) additional time → an admissible program solving Problem 1 whose every run halts within C(nd² + nk³) + C(ndk + k⁴log⁷(k/δ)) + C steps; reason: two LearnGMM calls cost O(nd² + nk³) by Proposition 4; the total running time is the content of the claim on the machine of §2.1
--   - reading: 'for a universal constant C > 0' → ∃ C > 0 quantified before all parameters; reason: C is universal
--   - encoding: solves Problem 1 → SolvesProblem1: Model-1 (outer) measure of {x : TV(Law_P(x), π_x) > δ} ≤ δ; reason: P[TV ≤ δ] ≥ 1 − δ
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 24, Proposition 6; proof pp. 25–26

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_PolyVoting_dirichletMeasure
import Definitions.Def_GMMPostSamp_Main_Toolkit
import Definitions.Def_GMMPostSamp_Main_Model
import Definitions.Def_GMMPostSamp_Main_Machine

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Proposition 6 (p. 24): there are a program and a universal `C > 0` such that for
`δ ∈ (0, 1/6)`, `d ≥ C(k + log(1/δ))`, `σ² ≤ 1/(C log(n/δ))` and
`n ≥ C d³k¹¹(1 + σ⁸)/(τ⁶r²)` (`τ` of Proposition 4 at `δ²/24`, `r = 1/16` as in the proof), the
program solves Problem 1; its running time is that of two LearnGMM calls,
`C(nd² + nk³)`, plus `C(ndk + k⁴ log⁷(k/δ))`, plus `C`, on every run. -/
theorem proposition_6 : ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
    ∀ k d n : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ n → ∀ (σ a A δ : ℝ) (α : Fin k → ℝ),
      0 < σ → 0 < a → a ≤ A → (∀ i, α i ∈ Set.Icc a A) → 0 < δ → δ < 1 / 6 →
      let τ : ℝ := (1 / (A * k)) * ((δ ^ 2 / 24) / (8 * k)) ^ (1 / a)
      let r : ℝ := 1 / 16
      C * ((k : ℝ) + Real.log (1 / δ)) ≤ d →
      σ ^ 2 ≤ 1 / (C * Real.log (n / δ)) →
      C * ((d : ℝ) ^ 3 * (k : ℝ) ^ 11 * (1 + σ ^ 8) / (τ ^ 6 * r ^ 2)) ≤ n →
      (∀ x : Fin n → E d, Machine.HaltsWithin P (Machine.samplerInput σ δ α x)
          (C * (n * (d : ℝ) ^ 2 + n * (k : ℝ) ^ 3) +
            C * (n * d * k + (k : ℝ) ^ 4 * Real.log (k / δ) ^ 7) + C)) ∧
      Machine.SolvesProblem1 P k d n σ α δ := by sorry

end GMMPostSamp.Main
