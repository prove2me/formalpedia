-- Prove2me | Theorems.Thm_KingDiagonal_eq_27_28
-- name    : KingDiagonal.eq_27_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:11.507796+00:00
-- url     : https://prove2.me/theorems/cd32ada3-9ab8-4b7d-9587-19987e53bdcc
-- title:
--   Eqs. (27)–(28): $\mathrm{Tr}(V^*V)^pK^p \le \sum_i \nu_p(\Psi)^p((\Phi(A))^p)_{ii} = \nu_p(\Psi)^p\mathrm{Tr}(\Phi(A))^p$
-- statement:
--   Let $\Phi$ be a diagonal map on $n\times n$ matrices, $\Psi$ a completely positive map from $k\times k$ to $m\times m$ matrices, $\rho$ a state on $\mathbb C^n\otimes\mathbb C^k$ and $p\ge1$ real. With $V = \operatorname{diag}(V_1,\dots,V_n)$ and $K = \Phi(A)\otimes I'$ built from $\rho$ as in (16), (23), (24),
--
--   $$
--   \operatorname{Tr}(V^*V)^pK^p \;\le\; \sum_{i=1}^n \big(\nu_p(\Psi)\big)^p\big((\Phi(A))^p\big)_{ii} \;=\; \big(\nu_p(\Psi)\big)^p\operatorname{Tr}(\Phi(A))^p .
--   $$
--
--   This combines (26), the nonzero-spectrum fact and the block bound (18).
--
--   **Formalization Note** Traces and diagonal entries are compared through their real parts; $\nu_p(\Psi)^p$ is a real power of a nonnegative real.
--
--   Differences from the source:
--   - generalization: Ψ maps M_k to M_k (the proof writes the output dimension as k) → Ψ : Superop k m with an arbitrary finite output index type m; reason: the paper says 'any other CP map'; taking m = k gives the page's statement
--   - generalization: (11) divides by (α_iα_j)^{1/2}, tacitly assuming every α_i > 0 → every state, with (√(α_iα_j))⁻¹ read as 0 when α_iα_j = 0; reason: for states with all α_i > 0 the Lean τ is the page's τ; the remaining states are extra instances on which the claim is still true
--   - encoding: Ψ a completely positive map → FiniteKrausCP Ψ (Ψ = Σ_j E_j · E_jᴴ for finitely many E_j); reason: in finite dimension a linear map is completely positive iff it has a finite Kraus representation (Choi–Kraus); same maps
--   - encoding: real matrix powers X^p, X^{p/2}, X^{1/2} of positive semidefinite matrices → cfc (fun x : ℝ => x ^ p) X, cfc Real.sqrt X; reason: the continuous functional calculus gives the usual powers on PSD (Hermitian, nonnegative spectrum) matrices, the only inputs used
--   - encoding: ν_p(Φ) = sup_ρ ‖Φ(ρ)‖_p over states, ‖X‖_p = (Tr X^p)^{1/p} on PSD outputs, p real ≥ 1 → nu (ENNReal.ofReal p) Φ: real sSup over density matrices of schattenNorm = (Re Tr (XᴴX)^{p/2})^{1/p}; reason: for p ≥ 1 and the PSD outputs of a CP map this is the page's p-norm and supremum (the set is nonempty and bounded whenever the input type is nonempty)
--   - encoding: inequalities between traces (real numbers) → inequalities between real parts of complex traces; reason: the traces involved are of Hermitian (or products of PSD) matrices and are real; same values
-- source:
--   King, An application of a matrix inequality in quantum information theory, arXiv:quant-ph/0412046v1, eqs. (27)–(28), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48
import Definitions.Def_KingDiagonal_IsDiagonalMap
import Definitions.Def_KingDiagonal_weightMatrix
import Definitions.Def_KingDiagonal_tau
import Definitions.Def_KingDiagonal_sqrtBlockRow
import Definitions.Def_KingDiagonal_blockDiag

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48
open scoped Matrix Kronecker

namespace KingDiagonal

/-- King, arXiv:quant-ph/0412046v1, eqs. (27)–(28), p.7: for a diagonal map `Φ`, a CP map `Ψ`, a
state `ρ` on `C^{kn}` and `p ≥ 1`, with `V` (23) and `K = Φ(A) ⊗ I′` (24) built from `ρ` as in
Sec. 3,
`Tr (V*V)^p K^p ≤ Σ_{i=1}^n (ν_p(Ψ))^p ((Φ(A))^p)_{ii}` (27) `= (ν_p(Ψ))^p Tr (Φ(A))^p` (28).

**Formalization Note.** `ν_p` is `nu (ENNReal.ofReal p)`; `(ν_p(Ψ))^p` is a real power of a nonnegative
real. Traces and diagonal entries are compared through their real parts. `Ψ : M_k → M_m` is in finite
Kraus form with output dimension `m` arbitrary; states with some `α_i = 0` are included. -/
theorem eq_27_28 {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Φ : Superop n n) (hΦ : IsDiagonalMap Φ)
    (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (ρ : Matrix (n × k) (n × k) ℂ) (hρ : IsDensityMatrix ρ) (p : ℝ) (hp : 1 ≤ p) :
    let V : Matrix (n × m) (n × (n × m)) ℂ :=
      blockDiag (sqrtBlockRow (superopTensor (id : Superop n n) Ψ (tau ρ)))
    let K : Matrix (n × (n × m)) (n × (n × m)) ℂ :=
      Φ (weightMatrix ρ) ⊗ₖ (1 : Matrix (n × m) (n × m) ℂ)
    (cfc (fun x : ℝ => x ^ p) (Vᴴ * V) * cfc (fun x : ℝ => x ^ p) K).trace.re ≤
        ∑ i, nu (ENNReal.ofReal p) Ψ ^ p *
          (cfc (fun x : ℝ => x ^ p) (Φ (weightMatrix ρ)) i i).re ∧
      ∑ i, nu (ENNReal.ofReal p) Ψ ^ p *
          (cfc (fun x : ℝ => x ^ p) (Φ (weightMatrix ρ)) i i).re =
        nu (ENNReal.ofReal p) Ψ ^ p *
          (cfc (fun x : ℝ => x ^ p) (Φ (weightMatrix ρ))).trace.re := by sorry

end KingDiagonal
