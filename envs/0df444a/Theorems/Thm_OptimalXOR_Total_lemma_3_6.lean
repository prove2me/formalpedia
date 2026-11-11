-- Prove2me | Theorems.Thm_OptimalXOR_Total_lemma_3_6
-- name    : OptimalXOR.Total.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:27.409204+00:00
-- url     : https://prove2.me/theorems/f7705ed6-b4c3-4cd7-bfe7-b696f49f0001
-- title:
--   Lemma 3.6 (error reduction step) — $\varepsilon_0+\varepsilon_1\le\frac43\varepsilon$ and $I_0+I_1\le I+4+\frac{16}3\varepsilon K$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\{-1,1,*\}$ be a communication problem, let $k\ge1$ be an integer and $\mu\in\mathcal P(\operatorname{dom}F)$. Let $\pi$ be a protocol for $F^{\oplus2k}$ with
--   $$\varepsilon=\mathrm{err}_{\mu^{2k}}(\pi,F^{\oplus2k}),\qquad I=\mathrm{IC}(\pi,\mu^{2k}).$$
--   Suppose that a protocol $\rho$ for $F^{\oplus k}$ satisfies $\mathrm{err}(\rho,F^{\oplus k})\le1/5$ and $\mathrm{IC}(\rho)\le K$. Then there are protocols $\pi_0,\pi_1$ for $F^{\oplus k}$ such that, writing $\varepsilon_j=\mathrm{err}_{\mu^k}(\pi_j,F^{\oplus k})$ and $I_j=\mathrm{IC}(\pi_j,\mu^k)$,
--   $$\varepsilon_0+\varepsilon_1\le\tfrac43\,\varepsilon,\tag{3.4}$$
--   $$I_0+I_1\le I+4+\tfrac{16}3\,\varepsilon K.\tag{3.5}$$
--
--   One step of the recursion: a protocol for $2k$ copies splits into two protocols for $k$ copies whose errors sum to at most $4/3$ of the original and whose costs sum to the original plus a charge for the fallback.
--
--   Differences from the source:
--   - encoding: F : X × Y → {−1, 1, ∗} with nonempty dom F → F : X → Y → Option ℤˣ (none = ∗, ℤˣ = {−1, 1}, XOR = product) with the hypothesis (dom F).Nonempty; reason: Lean convention; the same problems, and the paper requires dom F ≠ ∅ (p. 12)
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: K with IC(ρ) ≤ K → K : ℝ≥0 with worstInfoCost ρ (xorPow F k) ≤ K; reason: IC(ρ) ≥ 0 forces K ≥ 0, so no instance of the paper is lost
--   - encoding: there are protocols π₀, π₁ → ∃ π₀ π₁ satisfying TranscriptDetermined; reason: 'protocol' carries the output convention
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 25 (PDF 27), Lemma 3.6, (3.4)–(3.5)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Lemma 3.6 (error reduction step), p. 25. Let `k ≥ 1`, `µ ∈ P(dom F)`, `π` a protocol for
`F^{⊕2k}` with `ε = err_{µ^{2k}}(π, F^{⊕2k})` and `I = IC(π, µ^{2k})`, and `ρ` a protocol for
`F^{⊕k}` with `err(ρ, F^{⊕k}) ≤ 1/5` and `IC(ρ) ≤ K`. Then there are protocols `π₀, π₁` for
`F^{⊕k}` with `ε₀ + ε₁ ≤ (4/3) ε` (3.4) and `I₀ + I₁ ≤ I + 4 + (16/3) ε K` (3.5), where
`εⱼ = err_{µᵏ}(πⱼ, F^{⊕k})` and `Iⱼ = IC(πⱼ, µᵏ)`. -/
theorem lemma_3_6 {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (F : X → Y → Option ℤˣ) (hF : (dom F).Nonempty) (k : ℕ) (hk : 1 ≤ k)
    (μ : PMF (X × Y)) (hμ : μ ∈ Distributions F)
    (π : Protocol (Fin (2 * k) → X) (Fin (2 * k) → Y) ℤˣ) (hπ : π.TranscriptDetermined)
    (ρ : Protocol (Fin k → X) (Fin k → Y) ℤˣ) (hρ : ρ.TranscriptDetermined) (K : NNReal)
    (hρerr : worstError ρ (xorPow F k) ≤ 1 / 5) (hρIC : worstInfoCost ρ (xorPow F k) ≤ K) :
    ∃ π₀ π₁ : Protocol (Fin k → X) (Fin k → Y) ℤˣ,
      π₀.TranscriptDetermined ∧ π₁.TranscriptDetermined ∧
      distError π₀ (pmfPow μ k) (xorPow F k) + distError π₁ (pmfPow μ k) (xorPow F k) ≤
        4 / 3 * distError π (pmfPow μ (2 * k)) (xorPow F (2 * k)) ∧
      infoCost π₀ (pmfPow μ k) + infoCost π₁ (pmfPow μ k) ≤
        infoCost π (pmfPow μ (2 * k)) + 4 +
          16 / 3 * distError π (pmfPow μ (2 * k)) (xorPow F (2 * k)) * K := by sorry

end OptimalXOR.Total
