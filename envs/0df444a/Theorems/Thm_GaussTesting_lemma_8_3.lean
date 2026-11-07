-- Prove2me | Theorems.Thm_GaussTesting_lemma_8_3
-- name    : GaussTesting.lemma_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:37.949724+00:00
-- url     : https://prove2.me/theorems/62cb4401-9a05-49b6-866e-d22aa8cef043
-- title:
--   Lemma 8.3 — the coherent gap: $\mathrm{spec}(\Xi)\subseteq[0,1/2]\cup\{1\}$
-- statement:
--   Let $\Xi=\Pi^{(1,2,3)}_{\mathrm{sym}}\,\Pi^{(1,2)}_{\mathrm{test}}\,\Pi^{(1,2,3)}_{\mathrm{sym}}$ be the symmetrized operator on three copies of the $n$-mode bosonic Fock space, with $\Pi_{\mathrm{test}}$ = $\Pi_{\mathrm{test},\mathrm{Coh}}$. Let $\lambda_1$ be the largest eigenvalue of $\Xi$ and $\lambda$ any other (distinct) eigenvalue. Then
--
--   $$
--   \lambda_1=1\qquad\text{and}\qquad\lambda\in[0,1/2] ,
--   $$
--
--   for every number of modes $n$. Hence $\Xi$ has spectral gap $1-1/2>1/3$, which is what Theorem 3.5 needs with $k=2$, $m=3$.
--
--   Differences from the source:
--   - reading: Let λ₁ be the largest eigenvalue of Ξ and λ any other (distinct) eigenvalue; then λ₁ = 1 and λ ∈ [0, c] → 1 is an eigenvalue of Ξ, and every point of spectrum ℂ Ξ other than 1 is real and lies in [0, c]; reason: on finite-dimensional spaces the two coincide; on ℓ²(ℕⁿ)^{⊗3} the spectrum reading is the one Theorem 3.5's gap hypothesis needs
--   - encoding: orthogonal projectors Π_test → closed subspaces K with Π_test = proj K; reason: every orthogonal projector is the projector onto its closed range
--   - encoding: the fermionic Fock space ⋀ℂⁿ and the bosonic Fock space ⋁ℂⁿ → ℓ²(Fin n → Fin 2) (Jordan–Wigner, 1 = occupied, 0-based modes) and ℓ²(Fin n → ℕ); ℋ^{⊗k} is ℓ²(Fin k → ι); reason: unitarily the same spaces; Lean convention
--   - encoding: Π_test,Coh = U_BS†(I ⊗ |0ⁿ⟩⟨0ⁿ|)U_BS → proj onto {f : (a_j ⊗ I − I ⊗ a_j) f = 0 for all j}, coefficientwise; reason: U_BS†(I ⊗ a_j)U_BS = (I ⊗ a_j − a_j ⊗ I)/√2, so this is the range of the projector
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Lemma 8.3, p.73

import Definitions.Def_GaussTesting_testCoh
import Definitions.Def_GaussTesting_xi

namespace GaussTesting

/-- **Lemma 8.3.** Let `λ₁` be the largest eigenvalue of `Ξ = Π^{(1,2,3)}_sym Π^{(1,2)}_test Π^{(1,2,3)}_sym`
and let `λ` be any other (distinct) eigenvalue of `Ξ`. Then `λ₁ = 1` and `λ ∈ [0, 1 / 2]`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Lemma 8.3, p.73. Here `Π_test = Π_test,Coh` (proof of Proposition 8.2, p.72) on `ℓ²(ℕⁿ)^{⊗3}`.

**Formalization Note.** `Ξ = xi (testCoh n) 1` (`k = 2` test registers, `m = 3`). The eigenvalue statement is
read as: `1` is an eigenvalue of `Ξ`, and every point of the spectrum of `Ξ` other than `1` is real and
lies in `[0, 1 / 2]`; this gives `λ₁ = 1` and `λ ∈ [0, 1 / 2]`, and is how the gap `1 − 1 / 2` enters
Theorem 3.5. -/
theorem lemma_8_3 (n : ℕ) :
    (∃ v, v ≠ 0 ∧ xi (testCoh n) 1 v = v) ∧
      ∀ z ∈ spectrum ℂ (xi (testCoh n) 1), z = 1 ∨ (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1 / 2) := by sorry

end GaussTesting
