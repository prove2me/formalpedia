-- Prove2me | Theorems.Thm_KnownFidelity_Rank_proposition_3_2
-- name    : KnownFidelity.Rank.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:51:03.345433+00:00
-- url     : https://prove2.me/theorems/a5e34803-3c8c-42e5-8ce6-d932f213bb5e
-- title:
--   Proposition 3.2 — support projection: risk $\le 10q\min\{q,h_\sigma\}/n$ and $\mathsf S_\sigma(\varepsilon)\le\lceil 30rh_\sigma/\varepsilon^2\rceil$
-- statement:
--   Let $\sigma$ be a known state on $\mathbb C^d$ (any ambient dimension) with $\operatorname{rank}\sigma=r$.
--
--   1. Under the promise $\operatorname{rank}\rho\le s$, with $q=\min\{r,s\}$: for every $n\ge1$ there is a measurement on $n$ copies with
--   $$\mathbb E\,\big|\widehat F-F(\rho,\sigma)\big|^2\le\frac{10q\min\{q,h_\sigma\}}{n}\quad\text{for every such }\rho .$$
--   2. For unrestricted $\rho$ the same holds with $q=r$.
--   3. In particular, for every $\varepsilon>0$, $\ \mathsf S_\sigma(\varepsilon)\le\lceil 30rh_\sigma/\varepsilon^2\rceil$.
--
--   The estimator measures each copy against the support projector of $\sigma$ and runs Theorem 1.1 in ambient dimension $r$; it gives the upper bound of Theorem 1.2.
--
--   Differences from the source:
--   - reading: there is an estimator (for every input of the stated class) → ∃ POVM with real outcomes, chosen before the input, ∀ input; reason: an estimator is a collective measurement plus classical post-processing, which a real-outcome POVM includes; the estimator does not know the unknown input (∀∃ would make the statement trivial)
--   - encoding: E|F̂ − ·|² (expectation) → lower Lebesgue integral of (x − v)² in [0, ∞] (mse); reason: a Bochner integral of a non-integrable square is 0 in Lean; the lower integral is the same expectation and never a junk value
--   - encoding: least number of copies S → infimum in ℕ∞ (⊤ when no n works), compared via Nat.ceil cast to ℕ∞ or in ℝ≥0∞; reason: in ℕ the empty infimum is 0, which would make upper bounds trivial
--   - encoding: S_σ(ε) for unrestricted ρ → copyComplexityUnr σ ε = S^{(≤d)}_σ(ε); reason: every state on ℂ^d has rank at most d
--   - encoding: a supplied rank bound s (a positive integer) → every s : ℕ; reason: for s = 0 no state satisfies the promise, so the clause is vacuous there
--   - encoding: In particular, S_σ(ε) ≤ ⌈30rh_σ/ε²⌉ (ε unqualified) → for every ε > 0; reason: at ε ≤ 0 the printed right-hand side is undefined (division by ε²)
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Proposition 3.2, p. 7 (PDF p. 9)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_mse
import Definitions.Def_KnownFidelity_Rank_fid
import Definitions.Def_KnownFidelity_Rank_hSigma
import Definitions.Def_KnownFidelity_Rank_copyComplexityUnr

open MeasureTheory
open scoped Matrix ComplexOrder

namespace KnownFidelity.Rank

/-- **Proposition 3.2 (Support projection).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Proposition 3.2, printed p. 7 (PDF p. 9): "Let rank σ = r, and put q = min{r, s} under
the promise rank ρ ≤ s; for unrestricted ρ, put q = r. There is an estimator from n ≥ 1 copies
with E|F̂ − F(ρ, σ)|² ≤ 10q min{q, h_σ}/n. (17) In particular, S_σ(ε) ≤ ⌈30rh_σ/ε²⌉."

Three clauses, for a state `σ` on `ℂ^d` of rank `r`, in any ambient dimension `d`:
(a) under the promise `rank ρ ≤ s`, with `q = min{r, s}`, for every `n ≥ 1` one POVM on `n`
copies has risk at most `10 q min{q, h_σ}/n` on every such `ρ`;
(b) for unrestricted `ρ`, the same with `q = r`;
(c) for every `ε > 0`, `S_σ(ε) ≤ ⌈30 r h_σ/ε²⌉`.

**Formalization Note.** `r = σ.rank`; the POVM is chosen before `ρ`; the risk is the lower
integral `mse`; `S_σ(ε) = copyComplexityUnr σ ε`. Clause (a) is stated for every `s : ℕ` (for
`s = 0` no state satisfies the promise). -/
theorem proposition_3_2 {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (hσ : QAlgorithms.IsDensityMatrix σ) :
    (∀ s n : ℕ, 1 ≤ n → ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ,
      ∀ (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ), ρ.rank ≤ s →
        mse n E ρ hρ (fid ρ σ) ≤
          ENNReal.ofReal (10 * (min σ.rank s : ℕ) * min ((min σ.rank s : ℕ) : ℝ) (hSigma σ) / n)) ∧
    (∀ n : ℕ, 1 ≤ n → ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ,
      ∀ (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ),
        mse n E ρ hρ (fid ρ σ) ≤
          ENNReal.ofReal (10 * σ.rank * min (σ.rank : ℝ) (hSigma σ) / n)) ∧
    ∀ ε : ℝ, 0 < ε →
      copyComplexityUnr σ ε ≤ ((⌈30 * σ.rank * hSigma σ / ε ^ 2⌉₊ : ℕ) : ℕ∞) := by sorry

end KnownFidelity.Rank
