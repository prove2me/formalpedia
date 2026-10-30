-- Prove2me | Theorems.Thm_KingDiagonal_product_state_lower_bound
-- name    : KingDiagonal.product_state_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:15:12.040267+00:00
-- url     : https://prove2.me/theorems/48d8db2f-7934-4540-90d0-1f6faab9be84
-- title:
--   Product-state lower bound: $\nu_p(\Phi)\,\nu_p(\Psi) \le \nu_p(\Phi\otimes\Psi)$
-- statement:
--   Let $\Phi$ be a completely positive map from $n\times n$ to $n'\times n'$ matrices and $\Psi$ a completely positive map from $k\times k$ to $m\times m$ matrices. Then for every real $p\ge1$,
--
--   $$
--   \nu_p(\Phi)\,\nu_p(\Psi) \le \nu_p(\Phi\otimes\Psi).
--   $$
--
--   This is "the inequality in the other direction", obtained in the paper by restricting the supremum defining $\nu_p(\Phi\otimes\Psi)$ to product states; with (30) it completes the proof of Theorem 4.
--
--   Differences from the source:
--   - generalization: Φ a diagonal map on M_n → Φ any CP map Superop n n' in finite Kraus form; reason: the product-state argument uses only complete positivity; a diagonal map is CP (Schur product theorem) with n' = n
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - encoding: Φ a completely positive map → FiniteKrausCP Φ; reason: Choi–Kraus: in finite dimension CP maps are exactly the finite Kraus forms; same maps
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: ν_p(Φ) = sup_ρ ‖Φ(ρ)‖_p over states, ‖X‖_p = (Tr X^p)^{1/p} on PSD outputs, p real ≥ 1 → nu (ENNReal.ofReal p) Φ: real sSup over density matrices of schattenNorm = (Re Tr (XᴴX)^{p/2})^{1/p}; reason: for p ≥ 1 and the PSD outputs of a CP map this is the page's p-norm and supremum (the set is nonempty and bounded whenever the input type is nonempty)
--   - encoding: Φ ⊗ Ψ and I ⊗ Ψ on n × n block matrices with k × k blocks → superopTensor Φ Ψ and superopTensor id Ψ on Matrix (n × k) (n × k) ℂ, block index first; reason: superopTensor is the matrix-unit extension, equal to Φ ⊗ Ψ for linear Φ, Ψ; same block layout as the page
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, Sec. 4, last sentence, p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, Sec. 4, last sentence, p.7: "The inequality in the other
direction follows easily by restricting to product states": for CP maps `Φ` and `Ψ` and every
`p ≥ 1`, `ν_p(Φ) ν_p(Ψ) ≤ ν_p(Φ ⊗ Ψ)`.

**Formalization Note.** Stated for any CP map `Φ : M_n → M_{n'}` (not only a diagonal one) and any CP
map `Ψ : M_k → M_m`, both in finite Kraus form (`FiniteKrausCP`). `ν_p` is `nu (ENNReal.ofReal p)` and
`Φ ⊗ Ψ` is `superopTensor Φ Ψ`. No index type is assumed nonempty. -/
theorem product_state_lower_bound {n n' k m : Type*} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] [Fintype k] [DecidableEq k] [Fintype m] [DecidableEq m]
    (Φ : Superop n n') (hΦ : FiniteKrausCP Φ) (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (p : ℝ) (hp : 1 ≤ p) :
    nu (ENNReal.ofReal p) Φ * nu (ENNReal.ofReal p) Ψ ≤
      nu (ENNReal.ofReal p) (superopTensor Φ Ψ) := by sorry

end KingDiagonal
