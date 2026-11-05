-- Prove2me | Theorems.Thm_LoPopescuCC_Dilution_tensorPow_schmidt_products
-- name    : LoPopescuCC.Dilution.tensorPow_schmidt_products
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:03.98745+00:00
-- url     : https://prove2.me/theorems/2fddf732-7527-49e9-a41d-c0debabe9e3c
-- title:
--   Proof of the Theorem, p. 5 — the Schmidt coefficients of $\psi^N$ are products with multinomial multiplicities
-- statement:
--   Let $\psi=\sum_{i<k}\sqrt{\lambda_i}\,\alpha_i\otimes\beta_i$ with $\lambda_i\ge0$ and $(\alpha_i)$, $(\beta_i)$ orthonormal, and let $N\in\mathbb N$. For strings $x\in\{0,\dots,k-1\}^N$ put $\alpha_x=\alpha_{x_1}\otimes\cdots\otimes\alpha_{x_N}$ and likewise $\beta_x$. Then:
--
--   1. the families $(\alpha_x)_x$ and $(\beta_x)_x$ are orthonormal;
--   2. the $N$-th tensor power across the cut $A^N:B^N$ is
--   $$
--   \psi^{N}=\sum_{x}\Big(\prod_{j=1}^{N}\sqrt{\lambda_{x_j}}\Big)\,\alpha_x\otimes\beta_x;
--   $$
--   3. the coefficient of $x$ depends only on the count vector of $x$;
--   4. for a count vector $n$ with $\sum_in_i=N$, exactly $N!/\prod_in_i!$ strings have count vector $n$.
--
--   So the Schmidt decomposition of $\psi^N$ is the product of that of $\psi$, and each coefficient is repeated as often as the size of a type class. This degeneracy is what the proof of the Theorem exploits.
--
--   Differences from the source:
--   - generalization: ψ = a|00⟩ + b|11⟩, coefficients a^k b^(N−k), multiplicity C(N,k) → an arbitrary Schmidt form with k terms, coefficients ∏_j √λ_{x_j}, multiplicity Nat.multinomial; reason: the page calls the two-term case an illustration of a general proof; k = 2, √λ_0 = a, √λ_1 = b gives the page's claim
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Proof of the Theorem, p. 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_LoPopescuCC_Dilution_tensorPowCut
import Definitions.Def_LoPopescuCC_Dilution_productVec
import Definitions.Def_LoPopescuCC_Dilution_typeCount

namespace LoPopescuCC.Dilution

/-- **The Schmidt coefficients of `ψ^N`** (Lo, Popescu, arXiv:quant-ph/9902045v2, Proof of the
Theorem, p. 5: "They have the form a^k b^{N−k} and are, in general, highly degenerate — the
coefficient a^k b^{N−k} appears C(N, k) times"). If `ψ = Σ_{i<k} √λ_i α_i ⊗ β_i` with `(α_i)`,
`(β_i)` orthonormal, then for `x` ranging over strings of `N` labels the product vectors `α_x`,
`β_x` are orthonormal, `ψ^N = Σ_x (∏_j √λ_{x_j}) α_x ⊗ β_x`, the coefficient depends on `x` only
through its count vector, and exactly `N! / ∏_i n_i!` strings have count vector `n`.

**Formalization Note** The page treats `ψ = a|00⟩ + b|11⟩`, calling it the case in which the
general idea "is best understood"; `k = 2`, `√λ_0 = a`, `√λ_1 = b` gives the page's statement. -/
theorem tensorPow_schmidt_products {a b : Type} [Fintype a] [Fintype b] {k : ℕ} (lam : Fin k → ℝ) (hlam : ∀ i, 0 ≤ lam i) (α : Fin k → EuclideanSpace ℂ a) (β : Fin k → EuclideanSpace ℂ b) (hα : Orthonormal ℂ α) (hβ : Orthonormal ℂ β) (ψ : EuclideanSpace ℂ (a × b)) (hψ : ψ = ∑ i, (Real.sqrt (lam i) : ℂ) • QAlgorithms.tensorVec (α i) (β i)) (N : ℕ) : Orthonormal ℂ (fun x : Fin N → Fin k => productVec α x) ∧ Orthonormal ℂ (fun x : Fin N → Fin k => productVec β x) ∧ tensorPowCut ψ N = ∑ x : Fin N → Fin k, ((∏ j, Real.sqrt (lam (x j)) : ℝ) : ℂ) • QAlgorithms.tensorVec (productVec α x) (productVec β x) ∧ (∀ x y : Fin N → Fin k, typeCount x = typeCount y → ∏ j, Real.sqrt (lam (x j)) = ∏ j, Real.sqrt (lam (y j))) ∧ ∀ n : Fin k → ℕ, ∑ i, n i = N → (Finset.univ.filter fun x : Fin N → Fin k => typeCount x = n).card = Nat.multinomial Finset.univ n := by sorry

end LoPopescuCC.Dilution
