-- Prove2me | Theorems.Thm_GaussTesting_lemma_6_4
-- name    : GaussTesting.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:58.582969+00:00
-- url     : https://prove2.me/theorems/5f4cbaa5-41ae-4afa-a7cb-319491709afd
-- title:
--   Lemma 6.4 — $V_2=\mathrm{Sym}^2(\mathcal H)$, and for $k\ge3$: $\psi^{\otimes k}\in V_k$ iff $\psi$ is bosonic Gaussian
-- statement:
--   Let $\mathcal H$ be the $n$-mode bosonic Fock space and $V_k=\overline{\mathrm{Span}}\{|\phi\rangle^{\otimes k}:\phi\text{ bosonic Gaussian}\}$ (6.11). Then:
--
--   1. for $k=2$, $V_2=\mathrm{Sym}^2(\mathcal H)$ (6.12);
--   2. for every $k\ge3$ and every state $|\psi\rangle\in\mathcal H$, $|\psi\rangle^{\otimes k}\in V_k$ if and only if $|\psi\rangle$ is bosonic Gaussian.
--
--   So no two-copy symmetric test can certify Gaussianity, while the projector onto $V_3$ is a three-copy test with perfect completeness whose accepted product states are exactly the Gaussian ones.
--
--   Differences from the source:
--   - encoding: the top irrep V^{J(n)}_{(k/2,…,k/2)} ≅ Span{|ϕ⟩^{⊗k} : ϕ bosonic Gaussian} (6.11) → V_k := the closed span of {ϕ^{⊗k} : ϕ ∈ G_b} (topIrrep n k); reason: Mathlib has no Jacobi-group representation; (6.11) identifies the irrep with this span, and its irreducibility is not used in Theorem 6.1
--   - reading: Span → closed span; reason: an irrep subspace is closed, and the algebraic span is not closed in infinite dimension
--   - reading: G_b (resp. G_{b,0}) = the orbit of |0ⁿ⟩ under (zero-mean) bosonic Gaussian unitaries → unit vectors annihilated, coefficientwise, by the transformed annihilators (r_j + i r_{n+j}) + Σ_k (S_{jk} + i S_{n+j,k}) v_k for some S ∈ Sp(2n, ℝ) and r ∈ ℝ²ⁿ (r = 0 for G_{b,0}); reason: ψ = U|0ⁿ⟩ iff U a_j U† ψ = 0 for all j; the equations determine ψ up to scale; Mathlib has no metaplectic representation on ℓ²(ℕⁿ)
--   - encoding: the fermionic Fock space ⋀ℂⁿ and the bosonic Fock space ⋁ℂⁿ → ℓ²(Fin n → Fin 2) (Jordan–Wigner, 1 = occupied, 0-based modes) and ℓ²(Fin n → ℕ); ℋ^{⊗k} is ℓ²(Fin k → ι); reason: unitarily the same spaces; Lean convention
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Lemma 6.4, eqs. (6.11)–(6.12), p.56

import Definitions.Def_GaussTesting_topIrrep
import Definitions.Def_GaussTesting_symSub

namespace GaussTesting

/-- **Lemma 6.4.** With `V_k = Span{|ϕ⟩^{⊗k} : |ϕ⟩ bosonic Gaussian}` (6.11): for `k = 2`,
`V₂ = Sym²(ℋ)` (6.12); and for `k ≥ 3`, for any state `|ψ⟩ ∈ ℋ`, `|ψ⟩^{⊗k} ∈ V_k` iff `|ψ⟩` is bosonic
Gaussian.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Lemma 6.4, eqs. (6.11)–(6.12), p.56.

**Formalization Note.** `V_k = topIrrep n k` is the closed span (6.11), used as the definition of the top
irrep `V^{J(n)}_{(k/2,…,k/2)}`; `ℋ = ℓ²(ℕⁿ)` is the `n`-mode bosonic Fock space; "state" is any unit
vector. The `k ≥ 3` clause is stated for every `k ≥ 3`. -/
theorem lemma_6_4 :
    (∀ n : ℕ, topIrrep n 2 = symSub (Fin n → ℕ) 2) ∧
      ∀ (n k : ℕ), 3 ≤ k → ∀ ψ : Ell2 (Fin n → ℕ), ‖ψ‖ = 1 →
        (tpow k ψ ∈ topIrrep n k ↔ ψ ∈ Gb n) := by sorry

end GaussTesting
