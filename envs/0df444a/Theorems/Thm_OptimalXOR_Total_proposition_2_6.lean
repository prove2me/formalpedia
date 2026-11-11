-- Prove2me | Theorems.Thm_OptimalXOR_Total_proposition_2_6
-- name    : OptimalXOR.Total.proposition_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:30.69406+00:00
-- url     : https://prove2.me/theorems/f3f1f045-f139-4d1e-9921-46fb98de6496
-- title:
--   Proposition 2.6 — $\mathrm{IC}_0(F)=0$ for row- and column-constant $F$, otherwise $\mathrm{IC}_\delta(F^n)\ge(1-h_2(\delta))n$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\{-1,1,*\}$ be a communication problem, and let $h_2(p)=-p\log_2p-(1-p)\log_2(1-p)$ be the binary entropy.
--
--   1. If every row and every column of $F$ has a constant value on its legal inputs, then $\mathrm{IC}_0(F)=0$.
--   2. Otherwise, for every $0\le\delta<1/2$ and every integer $n\ge1$,
--   $$\mathrm{IC}_\delta(F^n)\ge\big(1-h_2(\delta)\big)\,n.\tag{2.20}$$
--   3. For a total function, the first case occurs if and only if $F$ is constant.
--
--   The proposition separates the problems of zero information complexity from all others, and supplies the linear lower bound for the direct-sum problem.
--
--   Differences from the source:
--   - encoding: F : X × Y → {−1, 1, ∗} with nonempty dom F → F : X → Y → Option ℤˣ (none = ∗, ℤˣ = {−1, 1}, XOR = product) with the hypothesis (dom F).Nonempty; reason: Lean convention; the same problems, and the paper requires dom F ≠ ∅ (p. 12)
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: binary entropy h₂ in bits → SelectiveDPT.H2 p = Real.binEntropy p / Real.log 2 (published); reason: Mathlib's binEntropy is in nats; same function on [0, 1]
--   - encoding: every row and every column has a constant value on its legal inputs → RowsColumnsConstant F; reason: definition of the phrase
--   - encoding: for a total function, the first case occurs iff F is constant → for every G : X → Y → ℤˣ with F = total G: RowsColumnsConstant F ↔ ∃ c, ∀ x y, G x y = c; reason: Lean convention for 'F is total'
--   - encoding: (1 − h₂(δ)) n ≤ IC_δ(Fⁿ) → ENNReal.ofReal ((1 − h₂(δ)) n) ≤ IC (dirPow F n) δ; reason: (1 − h₂(δ)) n > 0 for 0 ≤ δ < 1/2, so ofReal is exact
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 18 (PDF 20), Proposition 2.6, (2.20)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity
import Definitions.Def_SelectiveDPT_H2

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Proposition 2.6, p. 18. If every row and every column of `F` is constant on its legal inputs,
then `IC_0(F) = 0`. Otherwise `IC_δ(Fⁿ) ≥ (1 − h₂(δ)) n` for every `0 ≤ δ < 1/2` and every `n ≥ 1`
(2.20). For a total function, the first case occurs if and only if `F` is constant. -/
theorem proposition_2_6 {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (F : X → Y → Option ℤˣ) (hF : (dom F).Nonempty) :
    (RowsColumnsConstant F → IC F 0 = 0) ∧
      (¬ RowsColumnsConstant F → ∀ δ : ℝ, 0 ≤ δ → δ < 1 / 2 → ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal ((1 - SelectiveDPT.H2 δ) * n) ≤ IC (dirPow F n) δ) ∧
      (∀ G : X → Y → ℤˣ, F = total G →
        (RowsColumnsConstant F ↔ ∃ c : ℤˣ, ∀ x y, G x y = c)) := by sorry

end OptimalXOR.Total
