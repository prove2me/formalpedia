-- Prove2me | Theorems.Thm_LockingAccInfo_eq11_bloch_representation
-- name    : LockingAccInfo.eq11_bloch_representation
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:40:59.531881+00:00
-- url     : https://prove2.me/theorems/36edc6b6-32b7-416c-a751-cb5ffceb37ce
-- title:
--   Eq. (11) — generalised Bloch representation, $\operatorname{tr}(\sigma^2)\le1$ and $\sum_{y\in\mathcal Y}\operatorname{tr}(\sigma_y\sigma)^2\le2^m$
-- statement:
--   Let $\sigma$ be a state (density matrix) on $(\mathbb C^2)^{\otimes m}$. Then $\sigma$ has the **generalised Bloch representation**
--
--   $$
--   \sigma=2^{-m}\sum_{y\in\{0,1,2,3\}^m}\operatorname{tr}(\sigma_y\sigma)\,\sigma_y ,
--   $$
--
--   where every coefficient $\operatorname{tr}(\sigma_y\sigma)$ is real. Moreover $\operatorname{tr}(\sigma^2)\le1$, and with $\mathcal Y=\{1,2,3\}^m$,
--
--   $$
--   \sum_{y\in\mathcal Y}\operatorname{tr}(\sigma_y\sigma)^2\le2^m .
--   $$
--
--   The last inequality is the input to the second inequality of (8) in the proof of Lemma 2.
--
--   Differences from the source:
--   - encoding: operators on (ℂ²)^{⊗m}, σ_y = σ_{y₁} ⊗ ⋯ ⊗ σ_{y_m}, Y = {1,2,3}^m → matrices indexed by Fin m → Fin 2, σ_y the entrywise product of Pauli entries, y : Fin m → Fin 3 with letters shifted by Fin.succ; reason: Lean convention; the same operators and the same tuples
--   - encoding: the coefficients tr(σ_yσ) are real-valued → the imaginary part of tr(σ_yσ) is 0; the squares in the last clause are of real parts; reason: the same statement for complex numbers
-- source:
--   König, Renner, Bariska, Maurer, Locking of accessible information and implications for the security of quantum cryptography, arXiv:quant-ph/0512021v2, Appendix, Eq. (11), p.5; §III, p.3 (sentence after (8))

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_QAlgorithms_Defs_Information
open QMaxCutSDP.Rounding (pauli pauliString)
open QAlgorithms (IsDensityMatrix)

namespace LockingAccInfo

/-- König, Renner, Bariska, Maurer, arXiv:quant-ph/0512021v2, Eq. (11), p.5: "every state σ on
(C2)⊗m can be written in the so-called generalised Bloch representation as
σ = 2^{−m} Σ_{y∈{0,1,2,3}^m} tr(σyσ) σy , (11) where the coefficients tr(σyσ) are real-valued";
together with the consequence used for Eq. (8), p.3: "tr(σ²) ≤ 1 for every state σ on (C2)⊗m,
which implies Σ_{y∈Y} tr(σyσ)² ≤ 2^m [cf. (11)]", where Y = {1, 2, 3}^m.

**Formalization Note.** A state is a density matrix (positive semidefinite, trace 1) on the
index type `Fin m → Fin 2`. "Real-valued" is stated as a vanishing imaginary part, and the squares
in the last clause are of the real parts. The tuples `y ∈ {1, 2, 3}^m` are `Fin m → Fin 3` with
letters shifted by `Fin.succ`. -/
theorem eq11_bloch_representation (m : ℕ) (σ : Matrix (Fin m → Fin 2) (Fin m → Fin 2) ℂ)
    (hσ : IsDensityMatrix σ) :
    σ = ((2 : ℂ) ^ m)⁻¹ • ∑ y : Fin m → Fin 4, (pauliString y * σ).trace • pauliString y ∧
    (∀ y : Fin m → Fin 4, (pauliString y * σ).trace.im = 0) ∧
    (σ * σ).trace.re ≤ 1 ∧
    ∑ y : Fin m → Fin 3, ((pauliString (fun i => (y i).succ) * σ).trace.re) ^ 2 ≤ 2 ^ m := by sorry

end LockingAccInfo
