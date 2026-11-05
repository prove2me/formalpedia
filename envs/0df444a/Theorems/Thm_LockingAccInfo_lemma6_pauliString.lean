-- Prove2me | Theorems.Thm_LockingAccInfo_lemma6_pauliString
-- name    : LockingAccInfo.lemma6_pauliString
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:01.579451+00:00
-- url     : https://prove2.me/theorems/6340fcea-e396-4ee2-bc7c-350c872a9608
-- title:
--   Lemma 6 (corrected: (iii) spectrum ⊆ {−1, 1}) — Hermiticity, traces, spectra and orthogonality of Pauli strings
-- statement:
--   Let $m\ge0$ and let $\sigma_y=\sigma_{y_1}\otimes\cdots\otimes\sigma_{y_m}$ for $y\in\{0,1,2,3\}^m$, with $\sigma_0=\mathrm{id}$ and $\sigma_1,\sigma_2,\sigma_3$ the Pauli matrices. For all $y,y'\in\{0,1,2,3\}^m$:
--
--   $$
--   \text{(i) } \sigma_y^\dagger=\sigma_y,\qquad \text{(ii) } \operatorname{tr}(\sigma_y)=2^m\delta_{y,0},\qquad \text{(iv) } \operatorname{tr}(\sigma_y^\dagger\sigma_{y'})=2^m\delta_{y,y'},
--   $$
--
--   and (iii) every eigenvalue of $\sigma_y$ is $1$ or $-1$, and for $y\ne0$ the set of eigenvalues is exactly $\{-1,1\}$.
--
--   These facts make $\{2^{-m/2}\sigma_y\}_y$ an orthonormal basis of the Hermitian operators on $m$ qubits for the Hilbert–Schmidt inner product, which is what the generalised Bloch representation (11) and the bound (8) rest on.
--
--   **Formalization Note** Clause (iii) is stated in corrected form: as printed it claims the eigenvalues are $\{-1,1\}$ for every $y$, which fails at $y=0$ where $\sigma_y=\mathrm{id}$.
--
--   Differences from the source:
--   - correction: (iii) the eigenvalues of σ_y are {−1, 1} → the spectrum of σ_y is contained in {−1, 1}, and equals {−1, 1} for y ≠ 0; reason: false at y = (0,…,0): σ_0⊗⋯⊗σ_0 = id has the single eigenvalue 1 (proved in the sanity file); (3) only uses y ≠ 0
--   - encoding: y ∈ {0,1,2,3}^m, operators on (ℂ²)^{⊗m}, δ_{y,y′} → y : Fin m → Fin 4, matrices indexed by Fin m → Fin 2, if-then-else; eigenvalues as the matrix spectrum over ℂ; reason: Lean convention; the same operators and values
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, Lemma 6, pp.4–5

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
open QMaxCutSDP.Rounding (pauli pauliString)
open scoped Matrix

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Lemma 6, pp.4–5: "The following
holds for all m-tuples y, y′ ∈ {0, 1, 2, 3}^m. (i) σ†y = σy (ii) tr(σy) = 2^m · δy,0. (iii) The
eigenvalues of σy are {−1, 1}. (iv) tr(σ†y σy′) = 2^m · δy,y′."

**Formalization Note.** `σ_y` is the published `QMaxCutSDP.Rounding.pauliString` (indices 0, 1,
2, 3 name id, X, Y, Z; `(ℂ²)^{⊗m}` indexed by `Fin m → Fin 2`; the tensor product is the
entrywise product of Pauli entries). (iii) as printed is false at `y = (0, …, 0)`, where `σ_y = id` has the
single eigenvalue 1; it is stated corrected: the spectrum of `σ_y` is contained in `{−1, 1}`, and
equals `{−1, 1}` for `y ≠ 0`. The spectrum is the algebra spectrum of the matrix over ℂ (its set
of eigenvalues). `0 : Fin m → Fin 4` is the all-zero tuple; `δ` is written with `if`. -/
theorem lemma6_pauliString (m : ℕ) (y y' : Fin m → Fin 4) :
    (pauliString y)ᴴ = pauliString y ∧
    (pauliString y).trace = (if y = 0 then (2 : ℂ) ^ m else 0) ∧
    ((∀ μ ∈ spectrum ℂ (pauliString y), μ = 1 ∨ μ = -1) ∧
      (y ≠ 0 → spectrum ℂ (pauliString y) = {1, -1})) ∧
    ((pauliString y)ᴴ * pauliString y').trace = (if y = y' then (2 : ℂ) ^ m else 0) := by sorry

end LockingAccInfo
