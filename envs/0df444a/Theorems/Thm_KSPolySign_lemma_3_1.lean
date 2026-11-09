-- Prove2me | Theorems.Thm_KSPolySign_lemma_3_1
-- name    : KSPolySign.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:17.667651+00:00
-- url     : https://prove2.me/theorems/b5f37007-f571-4d4f-b267-315f0fab9a0d
-- title:
--   Lemma 3.1 — normalization and signing transfer
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb C^{n\times n}$ be nonzero Hermitian matrices of rank one, $m\ge1$. Define
--   $$L=\sum_{i=1}^m|\mathrm{tr}[A_i]|,\qquad \varepsilon_i=\mathrm{sign}(\mathrm{tr}[A_i]),\qquad \bar A_i=\varepsilon_iA_i/L,\qquad \zeta=\Big\|\sum_{i=1}^m\bar A_i^2\Big\|.$$
--
--   1. Each $\bar A_i$ is positive semidefinite of rank one, $\sum_i\mathrm{tr}[\bar A_i]=1$, $(mn)^{-1}\le\zeta\le1$, and $\|\bar A_i\|\le\sqrt\zeta$.
--   2. For every $\tau\in\{-1,1\}^m$ the signs $\sigma_i=\varepsilon_i\tau_i$ satisfy
--   $$\Big\|\sum_i\sigma_iA_i\Big\| = L\,\Big\|\sum_i\tau_i\bar A_i\Big\|,\qquad \Big\|\sum_iA_i^2\Big\| = L^2\zeta.$$
--
--   Here $\|\cdot\|$ is the operator norm. The lemma reduces the signing problem to positive semidefinite rank-one matrices of total trace one.
--
--   **Formalization Note** The trace of a Hermitian matrix is real; the sign is taken of its real part.
--
--   Differences from the source:
--   - encoding: ε_i = sign(tr[A_i]) → 1 if re tr A_i > 0, else −1; reason: the trace of a nonzero Hermitian rank-one matrix is real and nonzero, so this is its sign
--   - encoding: nonzero rank-one matrices → rank = 1; reason: rank one implies nonzero; same instances
--   - encoding: signs τ ∈ {−1, 1}^m → real vectors with every entry 1 or −1; reason: Lean convention; same instances
--   - encoding: operator norm ‖·‖ induced by the Euclidean norm; ‖X‖^{1/2} → AgnosticTNS.opNorm (sup of ‖Xv‖ over the Euclidean unit ball); Real.sqrt; reason: Lean convention; same values
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.1, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 3.1 (Normalization and signing transfer).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.1, p.17 (PDF p.17).

Let `A_1, …, A_m ∈ ℂ^{n×n}` be nonzero Hermitian rank-one matrices, `m ≥ 1`. Put `L = ∑_i |tr A_i|`,
`ε_i = sign(tr A_i)`, `Ā_i = ε_i A_i / L`, `ζ = ‖∑_i Ā_i²‖`. (a) Each `Ā_i` is PSD of rank one,
`∑_i tr Ā_i = 1`, `(mn)⁻¹ ≤ ζ ≤ 1`, `‖Ā_i‖ ≤ √ζ`. (b) For every `τ ∈ {−1, 1}^m`, `σ_i = ε_iτ_i` gives
`‖∑ σ_iA_i‖ = L‖∑ τ_iĀ_i‖`, and `‖∑ A_i²‖ = L²ζ`.

**Formalization Note** `‖·‖` is the Euclidean operator norm (`AgnosticTNS.opNorm`, published); `‖X‖^{1/2}` is `Real.sqrt`. The trace of a Hermitian matrix is real, so `|tr A_i|` and
`sign(tr A_i)` use its real part; it is nonzero for a nonzero Hermitian rank-one matrix, so the sign is
`1` if the real part is positive and `−1` otherwise. Signs are the reals `±1`. -/
theorem lemma_3_1 (m n : ℕ) (hm : 1 ≤ m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).IsHermitian ∧ (A i).rank = 1) :
    let L : ℝ := ∑ i, |(A i).trace.re|
    let ε : Fin m → ℝ := fun i => if 0 < (A i).trace.re then 1 else -1
    let Abar : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((ε i / L : ℝ) : ℂ) • A i
    let ζ : ℝ := AgnosticTNS.opNorm (∑ i, Abar i * Abar i)
    ((∀ i, (Abar i).PosSemidef ∧ (Abar i).rank = 1) ∧ (∑ i, (Abar i).trace) = 1 ∧
        1 / ((m : ℝ) * n) ≤ ζ ∧ ζ ≤ 1 ∧ ∀ i, AgnosticTNS.opNorm (Abar i) ≤ Real.sqrt ζ) ∧
      (∀ τ : Fin m → ℝ, (∀ i, τ i = 1 ∨ τ i = -1) →
          AgnosticTNS.opNorm (∑ i, ((ε i * τ i : ℝ) : ℂ) • A i) =
            L * AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Abar i)) ∧
      AgnosticTNS.opNorm (∑ i, A i * A i) = L ^ 2 * ζ := by sorry

end KSPolySign
