-- Prove2me | Theorems.Thm_OptimalXOR_Total_lemma_3_7
-- name    : OptimalXOR.Total.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:26.615993+00:00
-- url     : https://prove2.me/theorems/c220f4a5-86d7-43bb-b282-2b83275ca0b0
-- title:
--   Lemma 3.7 (recursive decomposition) — $\mathrm{IC}_{N^{-\alpha}/10}(F,\mu)\le\frac{13}{5N}\mathrm{IC}_{1/10}(F^{\oplus N})+4+\frac{32}5N^{-\alpha}$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\{-1,1,*\}$ be a communication problem, and let $N\ge1$ be a power of two. Then, with $\alpha=\log_2(3/2)=0.5849\ldots$, every input distribution $\mu\in\mathcal P(\operatorname{dom}F)$ satisfies
--   $$\mathrm{IC}_{N^{-\alpha}/10}(F,\mu)\le\frac{13}{5N}\,\mathrm{IC}_{1/10}(F^{\oplus N})+4+\frac{32}5\,N^{-\alpha}.\tag{3.11}$$
--
--   The conclusion is distributional while the right-hand side is the worst-case information complexity; it is the core of the XOR lemma with constant additive loss.
--
--   Differences from the source:
--   - encoding: F : X × Y → {−1, 1, ∗} with nonempty dom F → F : X → Y → Option ℤˣ (none = ∗, ℤˣ = {−1, 1}, XOR = product) with the hypothesis (dom F).Nonempty; reason: Lean convention; the same problems, and the paper requires dom F ≠ ∅ (p. 12)
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: N ≥ 1 a power of two; α = log(3/2) with log binary → ∃ d : ℕ, N = 2 ^ d; α = Real.logb 2 (3/2); N^{−α} as a real power; reason: the paper's log is the binary logarithm (p. 12)
--   - encoding: 4 + (32/5) N^{−α} → ENNReal.ofReal (4 + 32/5 · N^{−α}); reason: positive, so ofReal is exact
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 26 (PDF 28), Lemma 3.7, (3.11)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Lemma 3.7 (recursive decomposition), p. 26. For `N ≥ 1` a power of two and
`α = log₂(3/2) = 0.5849…`, every input distribution `µ ∈ P(dom F)` satisfies
`IC_{N^{−α}/10}(F, µ) ≤ (13/(5N)) IC_{1/10}(F^{⊕N}) + 4 + (32/5) N^{−α}` (3.11). -/
theorem lemma_3_7 {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (F : X → Y → Option ℤˣ) (hF : (dom F).Nonempty) (N : ℕ) (hN : ∃ d : ℕ, N = 2 ^ d)
    (μ : PMF (X × Y)) (hμ : μ ∈ Distributions F) :
    distIC F ((N : ℝ) ^ (-Real.logb 2 (3 / 2)) / 10) μ ≤
      13 / (5 * (N : ℝ≥0∞)) * IC (xorPow F N) (1 / 10) +
        ENNReal.ofReal (4 + 32 / 5 * (N : ℝ) ^ (-Real.logb 2 (3 / 2))) := by sorry

end OptimalXOR.Total
