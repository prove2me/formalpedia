-- Prove2me | Theorems.Thm_OptimalXOR_Total_corollary_3_4
-- name    : OptimalXOR.Total.corollary_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:34.976389+00:00
-- url     : https://prove2.me/theorems/458b77c2-aa9c-4fcf-b4eb-a9f75430a3e4
-- title:
--   Corollary 3.4 — $\mathrm{IC}_{1/5}(F^{\oplus k})\le\frac{2k}N\mathrm{IC}_{1/10}(F^{\oplus N})+4$ for $k\mid N$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\{-1,1,*\}$ be a communication problem, and let $k,N\ge1$ be integers such that $k$ divides $N$. Then
--   $$\mathrm{IC}_{1/5}(F^{\oplus k})\le\frac{2k}{N}\,\mathrm{IC}_{1/10}(F^{\oplus N})+4.$$
--
--   Passing from an XOR of $N$ copies to an XOR of $k$ copies scales the worst-case information complexity by $2k/N$ up to an additive constant; these are the fallback protocols of the recursion.
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
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 24 (PDF 26), Corollary 3.4

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Corollary 3.4, p. 24. For integers `k, N ≥ 1` with `k ∣ N`,
`IC_{1/5}(F^{⊕k}) ≤ (2k/N) IC_{1/10}(F^{⊕N}) + 4`. -/
theorem corollary_3_4 {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (F : X → Y → Option ℤˣ) (hF : (dom F).Nonempty) (k N : ℕ) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hkN : k ∣ N) :
    IC (xorPow F k) (1 / 5) ≤ 2 * (k : ℝ≥0∞) / N * IC (xorPow F N) (1 / 10) + 4 := by sorry

end OptimalXOR.Total
