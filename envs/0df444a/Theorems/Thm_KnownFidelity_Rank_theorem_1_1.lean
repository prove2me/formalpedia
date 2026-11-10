-- Prove2me | Theorems.Thm_KnownFidelity_Rank_theorem_1_1
-- name    : KnownFidelity.Rank.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:43.231091+00:00
-- url     : https://prove2.me/theorems/53e59828-3308-4025-aff0-a815188c5543
-- title:
--   Theorem 1.1 — estimation with a rank bound: risk $\le 4s\min\{s,h_\sigma\}/(n+1)$ and $\mathsf S^{(\le s)}_\sigma(\varepsilon)\le\lceil 12s\min\{s,h_\sigma\}/\varepsilon^2\rceil$
-- statement:
--   Let $\sigma$ be a known state on $\mathbb C^d$ and let $s$ be a supplied integer with $1\le s\le d$. Then:
--
--   1. For every $n\ge1$ there is a collective measurement on $n$ copies with real outcome $\widehat F$ such that
--   $$\sup_{\operatorname{rank}\rho\le s}\ \mathbb E\,\big|\widehat F-F(\rho,\sigma)\big|^2\ \le\ \frac{4s\min\{s,h_\sigma\}}{n+1}.$$
--   2. Consequently, for every $\varepsilon>0$,
--   $$\mathsf S^{(\le s)}_\sigma(\varepsilon)\ \le\ \Big\lceil\frac{12s\min\{s,h_\sigma\}}{\varepsilon^2}\Big\rceil\ \le\ \Big\lceil\frac{12s^2}{\varepsilon^2}\Big\rceil .$$
--
--   This removes the extra factor $\varepsilon^{-2}$ from the earlier $O(s^2/\varepsilon^4)$ bound and is the upper half of Theorem 1.2.
--
--   Differences from the source:
--   - reading: there is an estimator (for every input of the stated class) → ∃ POVM with real outcomes, chosen before the input, ∀ input; reason: an estimator is a collective measurement plus classical post-processing, which a real-outcome POVM includes; the estimator does not know the unknown input (∀∃ would make the statement trivial)
--   - encoding: E|F̂ − ·|² (expectation) → lower Lebesgue integral of (x − v)² in [0, ∞] (mse); reason: a Bochner integral of a non-integrable square is 0 in Lean; the lower integral is the same expectation and never a junk value
--   - encoding: least number of copies S → infimum in ℕ∞ (⊤ when no n works), compared via Nat.ceil cast to ℕ∞ or in ℝ≥0∞; reason: in ℕ the empty infimum is 0, which would make upper bounds trivial
--   - encoding: Consequently, S^{(≤s)}_σ(ε) ≤ ⌈12s min{s, h_σ}/ε²⌉ (ε unqualified) → for every ε > 0; reason: at ε ≤ 0 the printed right-hand side is undefined (division by ε²)
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Theorem 1.1, p. 1 (PDF p. 3)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_mse
import Definitions.Def_KnownFidelity_Rank_fid
import Definitions.Def_KnownFidelity_Rank_hSigma
import Definitions.Def_KnownFidelity_Rank_copyComplexity

open MeasureTheory
open scoped Matrix ComplexOrder

namespace KnownFidelity.Rank

/-- **Theorem 1.1 (Estimation with a rank bound on the unknown state).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Theorem 1.1, printed p. 1 (PDF p. 3): "Let σ be a known state on C^d, and suppose
rank ρ ≤ s ≤ d, where s is a supplied positive integer. For every n ≥ 1, there is an estimator
satisfying sup_{rank ρ≤s} E|F̂ − F(ρ, σ)|² ≤ 4s min{s, h_σ}/(n + 1). (1) Consequently,
S^{(≤s)}_σ(ε) ≤ ⌈12s min{s, h_σ}/ε²⌉ ≤ ⌈12s²/ε²⌉."

Both clauses: (1) for every `n ≥ 1` one POVM on `n` copies works for every state `ρ` of rank at
most `s`; and, for every `ε > 0`, the two ceiling bounds on `S^{(≤s)}_σ(ε)`.

**Formalization Note.** `sup_ρ X(ρ) ≤ b` is written `∀ ρ, X(ρ) ≤ b` with the POVM chosen before
`ρ`. `F(ρ, σ) = fid ρ σ`, `h_σ = hSigma σ`, the risk is the lower integral `mse`, and
`S^{(≤s)}_σ(ε) = copyComplexity σ s ε ∈ ℕ∞`; ceilings are `Nat.ceil`. The "Consequently" clause
is stated for every `ε > 0` (at `ε ≤ 0` the printed right-hand side is undefined). -/
theorem theorem_1_1 {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : QAlgorithms.IsDensityMatrix σ)
    (s : ℕ) (hs : 1 ≤ s) (hsd : s ≤ d) :
    (∀ n : ℕ, 1 ≤ n → ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ,
      ∀ (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ), ρ.rank ≤ s →
        mse n E ρ hρ (fid ρ σ) ≤ ENNReal.ofReal (4 * s * min (s : ℝ) (hSigma σ) / (n + 1))) ∧
    ∀ ε : ℝ, 0 < ε →
      copyComplexity σ s ε ≤ ((⌈12 * s * min (s : ℝ) (hSigma σ) / ε ^ 2⌉₊ : ℕ) : ℕ∞) ∧
      ⌈12 * s * min (s : ℝ) (hSigma σ) / ε ^ 2⌉₊ ≤ ⌈12 * (s : ℝ) ^ 2 / ε ^ 2⌉₊ := by sorry

end KnownFidelity.Rank
