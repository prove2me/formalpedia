-- Prove2me | Theorems.Thm_OptimalXOR_Total_fact_3_3
-- name    : OptimalXOR.Total.fact_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:20.302208+00:00
-- url     : https://prove2.me/theorems/c7bdcfae-556a-470c-8371-44c9e5e268d4
-- title:
--   Fact 3.3 (Error-preserving embedding) — $\mathrm{IC}_\varepsilon(G,\nu)\le I/t+2$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $G:\mathcal X\times\mathcal Y\to\{-1,1,*\}$ be a communication problem. Let $\nu\in\mathcal P(\operatorname{dom}G)$, let $t\ge1$ be an integer, and let $\pi$ be a protocol with $\mathrm{err}_{\nu^t}(\pi,G^{\oplus t})\le\varepsilon$ and $\mathrm{IC}(\pi,\nu^t)\le I$. Then
--   $$\mathrm{IC}_\varepsilon(G,\nu)\le\frac It+2.$$
--
--   A protocol for an XOR of $t$ copies yields a protocol for one copy with the same distributional error and a $1/t$ share of the information, up to two extra bits.
--
--   Differences from the source:
--   - encoding: F : X × Y → {−1, 1, ∗} with nonempty dom F → F : X → Y → Option ℤˣ (none = ∗, ℤˣ = {−1, 1}, XOR = product) with the hypothesis (dom F).Nonempty; reason: Lean convention; the same problems, and the paper requires dom F ≠ ∅ (p. 12)
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: I/t + 2 → ENNReal.ofReal (I / t + 2); reason: I ≥ IC(π, νᵗ) ≥ 0, so the value is positive and ofReal is exact
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 23 (PDF 25), Fact 3.3

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Fact 3.3 (Error-preserving embedding), p. 23. Let `ν ∈ P(dom G)`, `t ≥ 1`, and let `π` be a
protocol with `err_{νᵗ}(π, G^{⊕t}) ≤ ε` and `IC(π, νᵗ) ≤ I`. Then `IC_ε(G, ν) ≤ I/t + 2`. -/
theorem fact_3_3 {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (G : X → Y → Option ℤˣ) (hG : (dom G).Nonempty) (ν : PMF (X × Y))
    (hν : ν ∈ Distributions G) (t : ℕ) (ht : 1 ≤ t)
    (π : Protocol (Fin t → X) (Fin t → Y) ℤˣ) (hπ : π.TranscriptDetermined) (ε I : ℝ)
    (herr : distError π (pmfPow ν t) (xorPow G t) ≤ ε) (hI : infoCost π (pmfPow ν t) ≤ I) :
    distIC G ε ν ≤ ENNReal.ofReal (I / t + 2) := by sorry

end OptimalXOR.Total
