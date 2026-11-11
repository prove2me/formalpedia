-- Prove2me | Theorems.Thm_OptimalXOR_Total_lemma_3_11
-- name    : OptimalXOR.Total.lemma_3_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:46.643762+00:00
-- url     : https://prove2.me/theorems/2a0766cf-95a4-43ba-b161-7c38163da942
-- title:
--   Lemma 3.11 — $\mathrm{IC}_{1/3}(F^{\oplus n})\ge\frac n{48}(1-h_2(1/3))$ for $F$ not XOR-reducible
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\{-1,1\}$ be a (total) communication problem that is not XOR-reducible, that is, $F(x,y)\neq a(x)b(y)$ for all $a:\mathcal X\to\{-1,1\}$, $b:\mathcal Y\to\{-1,1\}$. Then for every integer $n\ge1$,
--   $$\mathrm{IC}_{1/3}(F^{\oplus n})\ge\frac{n}{48}\Big(1-h_2\big(\tfrac13\big)\Big).$$
--
--   The linear lower bound for XOR powers that, with Theorem 3.9, gives the multiplicative XOR lemma; it fails exactly for the XOR-reducible functions.
--
--   Differences from the source:
--   - encoding: total F : X × Y → {−1, 1} → F : X → Y → ℤˣ, used as the problem total F = fun x y => some (F x y); reason: Lean convention; dom (total F) = X × Y
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: binary entropy h₂ in bits → SelectiveDPT.H2 p = Real.binEntropy p / Real.log 2 (published); reason: Mathlib's binEntropy is in nats; same function on [0, 1]
--   - encoding: (n/48)(1 − h₂(1/3)) ≤ IC_{1/3}(F^{⊕n}) → ENNReal.ofReal ((n/48)(1 − h₂(1/3))) ≤ IC (xorPow (total F) n) (1/3); reason: 1 − h₂(1/3) > 0, so ofReal is exact
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 29 (PDF 31), Lemma 3.11

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity
import Definitions.Def_SelectiveDPT_H2

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Lemma 3.11, p. 29. If `F : X × Y → {−1, 1}` is not XOR-reducible, then for every integer
`n ≥ 1`, `IC_{1/3}(F^{⊕n}) ≥ (n/48)(1 − h₂(1/3))`. -/
theorem lemma_3_11 {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (F : X → Y → ℤˣ) (hF : ¬ XORReducible F) (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (n / 48 * (1 - SelectiveDPT.H2 (1 / 3))) ≤
      IC (xorPow (total F) n) (1 / 3) := by sorry

end OptimalXOR.Total
