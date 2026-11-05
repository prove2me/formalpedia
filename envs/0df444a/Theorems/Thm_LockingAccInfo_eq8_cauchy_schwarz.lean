-- Prove2me | Theorems.Thm_LockingAccInfo_eq8_cauchy_schwarz
-- name    : LockingAccInfo.eq8_cauchy_schwarz
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:15.151247+00:00
-- url     : https://prove2.me/theorems/3e9b179c-e534-498f-88ca-d91c6329d976
-- title:
--   Eq. (8) — $\frac1{|\mathcal Y|}\sum_y|\operatorname{tr}(\sigma_y\sigma)|\le\frac1{\sqrt{|\mathcal Y|}}\sqrt{\sum_y\operatorname{tr}(\sigma_y\sigma)^2}\le(2/3)^{m/2}$
-- statement:
--   Let $\mathcal Y=\{1,2,3\}^m$ and let $\sigma$ be a state on $(\mathbb C^2)^{\otimes m}$. Then
--
--   $$
--   \frac1{|\mathcal Y|}\sum_{y\in\mathcal Y}\bigl|\operatorname{tr}(\sigma_y\sigma)\bigr|\;\le\;\frac1{\sqrt{|\mathcal Y|}}\sqrt{\sum_{y\in\mathcal Y}\operatorname{tr}(\sigma_y\sigma)^2}\;\le\;\Bigl(\frac23\Bigr)^{m/2}.
--   $$
--
--   Both inequalities are asserted. Together with (6), (7) and Lemma 5 this yields Lemma 2: no state has large overlap with many of the $3^m$ Pauli strings at once.
--
--   Differences from the source:
--   - generalization: m ≥ 1 (the m of Section III) → every m ∈ ℕ; reason: (8) does not involve the states (3); at m = 0 all three sides equal 1, and the statement specializes to the paper's for m ≥ 1
--   - encoding: tr(σ_yσ) (real-valued for a state σ) → the real part of tr(σ_yσ); reason: tr(σ_yσ) is real for a state (Eq. (11)); same numbers
--   - encoding: (2/3)^{m/2} → Real.rpow (2/3) ((m : ℝ)/2); reason: the real power with a real exponent, not natural-number division
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, §III, Eq. (8), p.3

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_QAlgorithms_Defs_Information
open QMaxCutSDP.Rounding (pauli pauliString)
open QAlgorithms (IsDensityMatrix)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Eq. (8), p.3:
"(1/|Y|) Σ_{y∈Y} |tr(σyσ)| ≤ (1/√|Y|) √(Σ_{y∈Y} tr(σyσ)²) ≤ (2/3)^{m/2} , (8)" for every state σ
on (C2)⊗m, with Y = {1, 2, 3}^m. Both inequalities are stated.

**Formalization Note.** |Y| is the cardinality of `Fin m → Fin 3`, σy for y ∈ {1, 2, 3}^m is
`pauliString` with letters shifted by `Fin.succ`, and tr(σyσ) (real for a state) is taken as its
real part. `(2/3)^{m/2}` is the real power with exponent `(m : ℝ)/2`. No `1 ≤ m` is assumed:
(8) does not involve the operators (3), and at `m = 0` all three sides equal 1. -/
theorem eq8_cauchy_schwarz (m : ℕ) (σ : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)
    (hσ : IsDensityMatrix σ) :
    (1 / (Fintype.card (Fin m → Fin 3) : ℝ)) *
        ∑ y : Fin m → Fin 3, |(pauliString (fun i => (y i).succ) * σ).trace.re| ≤
      (1 / Real.sqrt (Fintype.card (Fin m → Fin 3) : ℝ)) *
        Real.sqrt (∑ y : Fin m → Fin 3, ((pauliString (fun i => (y i).succ) * σ).trace.re) ^ 2) ∧
    (1 / Real.sqrt (Fintype.card (Fin m → Fin 3) : ℝ)) *
        Real.sqrt (∑ y : Fin m → Fin 3, ((pauliString (fun i => (y i).succ) * σ).trace.re) ^ 2) ≤
      (2 / 3 : ℝ) ^ ((m : ℝ) / 2) := by sorry

end LockingAccInfo
