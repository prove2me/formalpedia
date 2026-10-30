-- Prove2me | Theorems.Thm_KingDiagonal_theorem_4
-- name    : KingDiagonal.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:22.705148+00:00
-- url     : https://prove2.me/theorems/8cd633a5-55ab-4dc0-8edf-f56ab6068fff
-- title:
--   Theorem 4: $\nu_p(\Phi\otimes\Psi) = \nu_p(\Phi)\,\nu_p(\Psi)$ for diagonal $\Phi$, any CP $\Psi$, all $p\ge1$
-- statement:
--   Let $\Phi$ be a diagonal map on $n\times n$ complex matrices, i.e. $\Phi(\rho) = C*\rho$ (Hadamard product) for a positive semidefinite $C$, and let $\Psi$ be any completely positive map from $k\times k$ to $m\times m$ complex matrices. Then for every real $p \ge 1$,
--
--   $$
--   \nu_p(\Phi\otimes\Psi) = \nu_p(\Phi)\,\nu_p(\Psi),
--   $$
--
--   where $\nu_p(\Theta) = \sup_\rho \|\Theta(\rho)\|_p = \sup_\rho \big(\operatorname{Tr}\Theta(\rho)^p\big)^{1/p}$ is the maximal output $p$-norm, the supremum running over states (positive semidefinite, trace one) in the domain of $\Theta$.
--
--   This is King's main result: the maximal output $p$-norm is multiplicative for the diagonal class and an arbitrary partner, for every $p \ge 1$. Since the derivative of $\nu_p$ at $p = 1$ is the negative minimal output entropy, it implies additivity of the minimal output entropy for a diagonal channel and any channel. Neither map is assumed trace preserving.
--
--   **Formalization Note** $\nu_p$ is the real supremum of the Schatten $p$-norm $(\operatorname{Tr}(X^*X)^{p/2})^{1/p}$ over density matrices; the tensor product of maps is defined through matrix units on $n\times k$ indices (block index first). No index type is assumed nonempty: with an empty input there are no states and both sides are $0$.
--
--   Differences from the source:
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: ν_p(Φ) = sup_ρ ‖Φ(ρ)‖_p over states, ‖X‖_p = (Tr X^p)^{1/p} on PSD outputs, p real ≥ 1 → nu (ENNReal.ofReal p) Φ: real sSup over density matrices of schattenNorm = (Re Tr (XᴴX)^{p/2})^{1/p}; reason: for p ≥ 1 and the PSD outputs of a CP map this is the page's p-norm and supremum (the set is nonempty and bounded whenever the input type is nonempty)
--   - encoding: Φ ⊗ Ψ and I ⊗ Ψ on n × n block matrices with k × k blocks → superopTensor Φ Ψ and superopTensor id Ψ on Matrix (n × k) (n × k) ℂ, block index first; reason: superopTensor is the matrix-unit extension, equal to Φ ⊗ Ψ for linear Φ, Ψ; same block layout as the page
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, Theorem 4, eq. (8), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_KingDiagonal_IsDiagonalMap

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48

namespace KingDiagonal

/-- King, *An application of a matrix inequality in quantum information theory*,
arXiv:quant-ph/0412046v1, Theorem 4, eq. (8), p.4: let `Φ` be a diagonal map, and let `Ψ` be any
other CP map. Then for all `p ≥ 1`, `ν_p(Φ ⊗ Ψ) = ν_p(Φ) ν_p(Ψ)`.

**Formalization Note.** `Φ : M_n → M_n` is diagonal in the sense of Definition 3 (`IsDiagonalMap`:
`Φ ρ = C ∗ ρ` with `C ⪰ 0`). `Ψ : M_k → M_m` is completely positive, written in finite Kraus form
(`FiniteKrausCP`, equivalent to complete positivity in finite dimension); its output dimension `m`
may differ from `k`; trace preservation is not assumed (p.3). `ν_p` is `nu (ENNReal.ofReal p)`, the
real supremum over density matrices (PSD, trace 1) of the Schatten `p`-norm
`(Tr (X*X)^{p/2})^{1/p}` of the output (3); `Φ ⊗ Ψ` is `superopTensor Φ Ψ` on
`Matrix (n × k) (n × k) ℂ`, first factor `n`. Every real `p ≥ 1` is covered, `p = 1` included, and no
index type is assumed nonempty. -/
theorem theorem_4 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Φ : Superop n n) (hΦ : IsDiagonalMap Φ)
    (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ) (p : ℝ) (hp : 1 ≤ p) :
    nu (ENNReal.ofReal p) (superopTensor Φ Ψ) =
      nu (ENNReal.ofReal p) Φ * nu (ENNReal.ofReal p) Ψ := by sorry

end KingDiagonal
