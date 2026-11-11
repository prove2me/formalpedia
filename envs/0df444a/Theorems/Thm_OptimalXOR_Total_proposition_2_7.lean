-- Prove2me | Theorems.Thm_OptimalXOR_Total_proposition_2_7
-- name    : OptimalXOR.Total.proposition_2_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:43.915677+00:00
-- url     : https://prove2.me/theorems/f8c60bfa-4a21-406d-8451-530dd925ccf6
-- title:
--   Proposition 2.7 — $\mathrm{IC}_\varepsilon(F^{\oplus n})\ge\mathrm{IC}_\varepsilon(F)$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\{-1,1,*\}$ be a communication problem. Then for every integer $n\ge1$ and every $\varepsilon\ge0$,
--   $$\mathrm{IC}_\varepsilon(F^{\oplus n})\ge\mathrm{IC}_\varepsilon(F).\tag{2.24}$$
--
--   The XOR of $n$ copies is at least as hard as one copy; with Proposition 2.6 this rules out additive losses in the XOR lemma.
--
--   Differences from the source:
--   - encoding: F : X × Y → {−1, 1, ∗} with nonempty dom F → F : X → Y → Option ℤˣ (none = ∗, ℤˣ = {−1, 1}, XOR = product) with the hypothesis (dom F).Nonempty; reason: Lean convention; the same problems, and the paper requires dom F ≠ ∅ (p. 12)
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 19 (PDF 21), Proposition 2.7, (2.24)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Proposition 2.7, p. 19. For every integer `n ≥ 1` and every `ε ≥ 0`,
`IC_ε(F^{⊕n}) ≥ IC_ε(F)` (2.24). -/
theorem proposition_2_7 {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (F : X → Y → Option ℤˣ) (hF : (dom F).Nonempty) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 ≤ ε) :
    IC F ε ≤ IC (xorPow F n) ε := by sorry

end OptimalXOR.Total
