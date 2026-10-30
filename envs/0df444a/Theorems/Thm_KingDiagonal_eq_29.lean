-- Prove2me | Theorems.Thm_KingDiagonal_eq_29
-- name    : KingDiagonal.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:12.713354+00:00
-- url     : https://prove2.me/theorems/44f8dc73-b03d-4259-867b-f3f7dc7c7c38
-- title:
--   Eq. (29): $\mathrm{Tr}((\Phi\otimes\Psi)(\rho))^p \le \nu_p(\Psi)^p\,\nu_p(\Phi)^p$
-- statement:
--   Let $\Phi$ be a diagonal map on $n\times n$ matrices and $\Psi$ a completely positive map from $k\times k$ to $m\times m$ matrices. Then for every state $\rho$ on $\mathbb C^n\otimes\mathbb C^k$ and every real $p\ge1$,
--
--   $$
--   \operatorname{Tr}\big((\Phi\otimes\Psi)(\rho)\big)^p \le \big(\nu_p(\Psi)\big)^p\big(\nu_p(\Phi)\big)^p .
--   $$
--
--   Taking the supremum over $\rho$ and $p$-th roots gives the upper bound (30).
--
--   **Formalization Note** The power is the functional-calculus power of the positive semidefinite output; the trace is compared through its real part.
--
--   Differences from the source:
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: real matrix powers X^p, X^{p/2}, X^{1/2} of positive semidefinite matrices → cfc (fun x : ℝ => x ^ p) X, cfc Real.sqrt X; reason: the continuous functional calculus gives the usual powers on PSD (Hermitian, nonnegative spectrum) matrices, the only inputs used
--   - encoding: ν_p(Φ) = sup_ρ ‖Φ(ρ)‖_p over states, ‖X‖_p = (Tr X^p)^{1/p} on PSD outputs, p real ≥ 1 → nu (ENNReal.ofReal p) Φ: real sSup over density matrices of schattenNorm = (Re Tr (XᴴX)^{p/2})^{1/p}; reason: for p ≥ 1 and the PSD outputs of a CP map this is the page's p-norm and supremum (the set is nonempty and bounded whenever the input type is nonempty)
--   - encoding: inequalities between traces (real numbers) → inequalities between real parts of complex traces; reason: the traces involved are of Hermitian (or products of PSD) matrices and are real; same values
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (29), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_KingDiagonal_IsDiagonalMap

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48
open scoped Matrix

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (29), p.7: for a diagonal map `Φ`, a CP map `Ψ`, every state
`ρ` on `C^{kn}` and every `p ≥ 1`, `Tr ((Φ ⊗ Ψ)(ρ))^p ≤ (ν_p(Ψ))^p (ν_p(Φ))^p`.

**Formalization Note.** `Φ ⊗ Ψ` is `superopTensor Φ Ψ` (block index first), `ν_p` is
`nu (ENNReal.ofReal p)`, the matrix power is `cfc (fun x : ℝ => x ^ p)` applied to the positive
semidefinite output, and the trace is compared through its real part. `Ψ : M_k → M_m` is in finite
Kraus form with output dimension `m` arbitrary. -/
theorem eq_29 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Φ : Superop n n) (hΦ : IsDiagonalMap Φ)
    (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (ρ : Matrix (n × k) (n × k) ℂ) (hρ : IsDensityMatrix ρ) (p : ℝ) (hp : 1 ≤ p) :
    (cfc (fun x : ℝ => x ^ p) (superopTensor Φ Ψ ρ)).trace.re ≤
      nu (ENNReal.ofReal p) Ψ ^ p * nu (ENNReal.ofReal p) Φ ^ p := by sorry

end KingDiagonal
