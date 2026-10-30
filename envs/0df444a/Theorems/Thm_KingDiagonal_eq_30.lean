-- Prove2me | Theorems.Thm_KingDiagonal_eq_30
-- name    : KingDiagonal.eq_30
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:30.501011+00:00
-- url     : https://prove2.me/theorems/2b19d1f6-5d39-4a75-9bba-b0d432848011
-- title:
--   Eq. (30): $\nu_p(\Phi\otimes\Psi) \le \nu_p(\Phi)\,\nu_p(\Psi)$ for diagonal $\Phi$
-- statement:
--   Let $\Phi$ be a diagonal map on $n\times n$ matrices and $\Psi$ a completely positive map from $k\times k$ to $m\times m$ matrices. Then for every real $p \ge 1$,
--
--   $$
--   \nu_p(\Phi\otimes\Psi) \le \nu_p(\Phi)\,\nu_p(\Psi),
--   $$
--
--   where $\nu_p(\Theta) = \sup_\rho \|\Theta(\rho)\|_p$ is the maximal output $p$-norm (supremum over states). This is the nontrivial half of Theorem 4.
--
--   Differences from the source:
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: ν_p(Φ) = sup_ρ ‖Φ(ρ)‖_p over states, ‖X‖_p = (Tr X^p)^{1/p} on PSD outputs, p real ≥ 1 → nu (ENNReal.ofReal p) Φ: real sSup over density matrices of schattenNorm = (Re Tr (XᴴX)^{p/2})^{1/p}; reason: for p ≥ 1 and the PSD outputs of a CP map this is the page's p-norm and supremum (the set is nonempty and bounded whenever the input type is nonempty)
--   - encoding: Φ ⊗ Ψ and I ⊗ Ψ on n × n block matrices with k × k blocks → superopTensor Φ Ψ and superopTensor id Ψ on Matrix (n × k) (n × k) ℂ, block index first; reason: superopTensor is the matrix-unit extension, equal to Φ ⊗ Ψ for linear Φ, Ψ; same block layout as the page
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eq. (30), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_KingDiagonal_IsDiagonalMap

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eq. (30), p.7: for a diagonal map `Φ`, a CP map `Ψ` and every
`p ≥ 1`, `ν_p(Φ ⊗ Ψ) ≤ ν_p(Φ) ν_p(Ψ)`.

**Formalization Note.** `ν_p` is `nu (ENNReal.ofReal p)` (a real supremum over density matrices of
the Schatten `p`-norm of the output) and `Φ ⊗ Ψ` is `superopTensor Φ Ψ`. `Ψ : M_k → M_m` is in finite
Kraus form with output dimension `m` arbitrary; no index type is assumed nonempty. -/
theorem eq_30 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Φ : Superop n n) (hΦ : IsDiagonalMap Φ)
    (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ) (p : ℝ) (hp : 1 ≤ p) :
    nu (ENNReal.ofReal p) (superopTensor Φ Ψ) ≤
      nu (ENNReal.ofReal p) Φ * nu (ENNReal.ofReal p) Ψ := by sorry

end KingDiagonal
