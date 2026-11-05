-- Prove2me | Theorems.Thm_LoPopescuCC_Dilution_schmidt_decomposition_eigen
-- name    : LoPopescuCC.Dilution.schmidt_decomposition_eigen
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:28.747367+00:00
-- url     : https://prove2.me/theorems/7022d82a-1b97-4ff4-9f1f-8fc6066f5096
-- title:
--   Eq. (11) — Schmidt decomposition with eigenvectors of $\rho^A$, $\rho^B$ (corrected: $r\le\min(p,q)$)
-- statement:
--   Let $\mathcal H_A$ and $\mathcal H_B$ have dimensions $p$ and $q$, let $\psi\in\mathcal H_A\otimes\mathcal H_B$ be normalized, and let $\rho^A=\mathrm{Tr}_B|\psi\rangle\langle\psi|$ and $\rho^B=\mathrm{Tr}_A|\psi\rangle\langle\psi|$. Then there are $r$, numbers $\lambda_1,\dots,\lambda_r>0$ and orthonormal families $(a_i)$ in $\mathcal H_A$ and $(b_i)$ in $\mathcal H_B$ with
--
--   $$
--   \psi=\sum_{i=1}^{r}\sqrt{\lambda_i}\,a_i\otimes b_i,\qquad \rho^Aa_i=\lambda_ia_i,\qquad \rho^Bb_i=\lambda_ib_i,
--   $$
--
--   where $r=\operatorname{rank}\rho^A$ and $r\le\min(p,q)$.
--
--   This identifies the Schmidt coefficients with the spectrum of the reduced states, which is what connects the entropy $S$ in the Theorem to the Schmidt decomposition of $\psi^N$.
--
--   **Formalization Note** The existence half is the published `QAlgorithms.Papers.Independent.Frontier18.P17.pureState_schmidt`, which has no eigenvector clauses and no $r=\operatorname{rank}\rho^A$.
--
--   Differences from the source:
--   - correction: r < min(p, q) → r ≤ min(p, q); reason: the printed bound is false: the singlet has p = q = 2 and ρ^A = I/2, so r = 2 = min(p, q)
--   - encoding: Hilbert spaces of dimensions p and q → finite index types a, b with p = card a, q = card b, and vectors of EuclideanSpace; reason: a finite-dimensional Hilbert space with a chosen orthonormal basis; same instances
--   - encoding: r is the total dimension of the non-zero eigenspaces of ρ^A → r = Matrix.rank of ρ^A, with every λ_i > 0; reason: ρ^A is Hermitian, so its rank is that dimension; no zero terms occur in the sum
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, footnote [9], Eq. (11), p. 8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement

open scoped Matrix

namespace LoPopescuCC.Dilution

/-- **Schmidt decomposition, with `r ≤ min(p, q)`** (Lo, Popescu, arXiv:quant-ph/9902045v2, footnote
[9], Eq. (11), p. 8). A normalized `ψ ∈ H_A ⊗ H_B` can be written
`ψ = Σ_{i=1}^r √λ_i a_i ⊗ b_i` with `(a_i)`, `(b_i)` orthonormal, `a_i` an eigenvector of
`ρ^A = Tr_B |ψ⟩⟨ψ|` and `b_i` an eigenvector of `ρ^B = Tr_A |ψ⟩⟨ψ|`, both with eigenvalue `λ_i > 0`,
where `r` is the rank of `ρ^A`.

**Formalization Note** `ρ^A` is `QAlgorithms.traceRight (pureDensity ψ)` and `ρ^B` is
`QAlgorithms.traceLeft (pureDensity ψ)`. The footnote prints `r < min(p, q)`, which fails for the
singlet (`p = q = r = 2`); the statement has `r ≤ min(p, q)`. Its existence half is the published
`QAlgorithms.Papers.Independent.Frontier18.P17.pureState_schmidt`. -/
theorem schmidt_decomposition_eigen {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : EuclideanSpace ℂ (a × b)) (hψ : QAlgorithms.IsState ψ) : ∃ (r : ℕ) (lam : Fin r → ℝ) (α : Fin r → EuclideanSpace ℂ a) (β : Fin r → EuclideanSpace ℂ b), (∀ i, 0 < lam i) ∧ Orthonormal ℂ α ∧ Orthonormal ℂ β ∧ ψ = ∑ i, (Real.sqrt (lam i) : ℂ) • QAlgorithms.tensorVec (α i) (β i) ∧ (∀ i x, (QAlgorithms.traceRight (QAlgorithms.pureDensity ψ) *ᵥ (fun z => α i z)) x = (lam i : ℂ) * α i x) ∧ (∀ i y, (QAlgorithms.traceLeft (QAlgorithms.pureDensity ψ) *ᵥ (fun z => β i z)) y = (lam i : ℂ) * β i y) ∧ r = (QAlgorithms.traceRight (QAlgorithms.pureDensity ψ)).rank ∧ r ≤ min (Fintype.card a) (Fintype.card b) := by sorry

end LoPopescuCC.Dilution
