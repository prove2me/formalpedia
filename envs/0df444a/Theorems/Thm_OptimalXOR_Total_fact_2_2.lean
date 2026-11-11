-- Prove2me | Theorems.Thm_OptimalXOR_Total_fact_2_2
-- name    : OptimalXOR.Total.fact_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:26.807232+00:00
-- url     : https://prove2.me/theorems/b0b3e00d-0d39-4254-a8f9-25cf6a026ba1
-- title:
--   Fact 2.2 (Minimax theorem) — $\mathrm{IC}_{\varepsilon/\alpha}(F)\le\mathrm{IC}^D_\varepsilon(F)/(1-\alpha)$ and $\mathrm{IC}_{2\varepsilon}(F)\le2\,\mathrm{IC}^D_\varepsilon(F)$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $F:\mathcal X\times\mathcal Y\to\mathcal Z\cup\{*\}$ be a communication problem with a finite nonempty output set $\mathcal Z$. Then for every $\varepsilon>0$ and $\alpha\in(0,1)$,
--   $$\mathrm{IC}_{\varepsilon/\alpha}(F)\le\frac{\mathrm{IC}^D_\varepsilon(F)}{1-\alpha},\qquad\text{in particular}\qquad \mathrm{IC}_{2\varepsilon}(F)\le 2\,\mathrm{IC}^D_\varepsilon(F).\tag{2.13}$$
--
--   This is Braverman's minimax theorem, extended to arbitrary promise domains: it converts a bound on the distributional information complexity under every input distribution into a single protocol whose worst-case error and worst-case information cost are both controlled.
--
--   Differences from the source:
--   - encoding: F : X × Y → Z ∪ {∗} with nonempty dom F → F : X → Y → Option Z (none = ∗) with the hypothesis (dom F).Nonempty; reason: Lean convention; the same problems, and the paper requires dom F ≠ ∅ (p. 12)
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: output set Z of a communication problem → [Fintype Z] [Nonempty Z]; reason: the standing assumption that all sets are finite and nonempty
--   - encoding: IC^D_ε(F)/(1 − α) → distMaxIC F ε / ENNReal.ofReal (1 − α) in ℝ≥0∞; reason: 1 − α ∈ (0, 1), so this is the paper's quotient
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 15 (PDF 17), Fact 2.2, (2.13)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Fact 2.2 (Minimax theorem), p. 15. For a communication problem `F` with output set `Z`,
every `ε > 0` and `α ∈ (0, 1)`: `IC_{ε/α}(F) ≤ IC^D_ε(F)/(1 − α)`; in particular
`IC_{2ε}(F) ≤ 2 IC^D_ε(F)` (2.13). -/
theorem fact_2_2 {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    [Fintype Z] [Nonempty Z] (F : X → Y → Option Z) (hF : (dom F).Nonempty)
    (ε α : ℝ) (hε : 0 < ε) (hα₀ : 0 < α) (hα₁ : α < 1) :
    IC F (ε / α) ≤ distMaxIC F ε / ENNReal.ofReal (1 - α) ∧
      IC F (2 * ε) ≤ 2 * distMaxIC F ε := by sorry

end OptimalXOR.Total
