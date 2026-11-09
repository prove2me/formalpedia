-- Prove2me | Theorems.Thm_KSPolySign_lemma_4_8
-- name    : KSPolySign.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:11.307106+00:00
-- url     : https://prove2.me/theorems/dc4daf33-0839-4bb9-9862-ca043afcf4f5
-- title:
--   Lemma 4.8 — coefficient contraction
-- statement:
--   Let $C_1,\dots,C_k$ be positive semidefinite matrices of rank at most one with $\sum_iC_i^2\preceq I$.
--
--   1. For every Hermitian $D$, $\displaystyle\sum_i\mathrm{tr}[C_iD]^2\le\mathrm{tr}\Big[D^2\sum_iC_i^2\Big]\le\|D\|_F^2$.
--   2. For every $r\in\mathbb R^k$, $\displaystyle\Big\|\sum_ir_iC_i\Big\|\le\Big\|\sum_ir_iC_i\Big\|_F\le\|r\|_2$.
--
--   The variance bound turns Euclidean errors in the coefficients into Frobenius-norm errors in the matrix sum.
--
--   **Formalization Note** The traces in (1) are real for Hermitian arguments; their real parts are taken. $\|X\|_F=(\sum_{j,l}|X_{jl}|^2)^{1/2}$.
--
--   Differences from the source:
--   - encoding: tr[C_iD], tr[D²∑C_i²] → real parts of these traces; reason: the traces are real for Hermitian arguments; same values
--   - encoding: operator norm ‖·‖ induced by the Euclidean norm; ‖X‖^{1/2} → AgnosticTNS.opNorm (sup of ‖Xv‖ over the Euclidean unit ball); Real.sqrt; reason: Lean convention; same values
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.8, p.41 (PDF p.41)

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 4.8 (Coefficient contraction).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.8, p.41 (PDF p.41).

Let `C_1, …, C_k` be PSD of rank at most one with `∑ C_i² ⪯ I`. (a) For every Hermitian `D`,
`∑_i tr[C_iD]² ≤ tr[D² ∑_i C_i²] ≤ ‖D‖_F²`. (b) For every `r ∈ ℝ^k`, `‖∑ r_iC_i‖ ≤ ‖∑ r_iC_i‖_F ≤ ‖r‖₂`.

**Formalization Note** The traces in (a) are of products of Hermitian matrices and are real; their real
parts are taken. `‖X‖_F = (∑_{j,l} |X_{jl}|²)^{1/2}`. `‖·‖` is the Euclidean operator norm (`AgnosticTNS.opNorm`, published); `‖X‖^{1/2}` is `Real.sqrt`. -/
theorem lemma_4_8 (n k : ℕ) (C : Fin k → Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ i, (C i).PosSemidef ∧ (C i).rank ≤ 1) (hsq : (1 - ∑ i, C i * C i).PosSemidef) :
    (∀ D : Matrix (Fin n) (Fin n) ℂ, D.IsHermitian →
      ∑ i, ((C i * D).trace.re) ^ 2 ≤ (D * D * ∑ i, C i * C i).trace.re ∧
        (D * D * ∑ i, C i * C i).trace.re ≤ ∑ j, ∑ l, ‖D j l‖ ^ 2) ∧
    ∀ r : Fin k → ℝ,
      AgnosticTNS.opNorm (∑ i, ((r i : ℝ) : ℂ) • C i) ≤ Real.sqrt (∑ j, ∑ l, ‖((∑ i, ((r i : ℝ) : ℂ) • C i)) j l‖ ^ 2) ∧
        Real.sqrt (∑ j, ∑ l, ‖((∑ i, ((r i : ℝ) : ℂ) • C i)) j l‖ ^ 2) ≤ Real.sqrt (∑ i, r i ^ 2) := by sorry

end KSPolySign
