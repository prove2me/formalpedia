-- Prove2me | Theorems.Thm_GaussTesting_theorem_4_2
-- name    : GaussTesting.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:01:03.455211+00:00
-- url     : https://prove2.me/theorems/63a37271-361b-462c-8e3d-bf8efa89660d
-- title:
--   Theorem 4.2 — the fermionic Gaussian gap: $\mathrm{spec}(\Xi)\subseteq[0,7/12]\cup\{1\}$
-- statement:
--   Let $\Xi=\Pi^{(1,2,3)}_{\mathrm{sym}}\,\Pi^{(1,2)}_{\mathrm{test}}\,\Pi^{(1,2,3)}_{\mathrm{sym}}$ be the symmetrized operator on three copies of the $n$-mode fermionic Fock space, with $\Pi_{\mathrm{test}}$ = $\Pi_{\mathrm{test},G_f}$, the projector onto $\ker\Lambda$. Let $\lambda_1$ be the largest eigenvalue of $\Xi$ and $\lambda$ any other (distinct) eigenvalue. Then
--
--   $$
--   \lambda_1=1\qquad\text{and}\qquad\lambda\in[0,7/12] ,
--   $$
--
--   for every number of modes $n$. Hence $\Xi$ has spectral gap $1-7/12>1/3$, which is what Theorem 3.5 needs with $k=2$, $m=3$.
--
--   Differences from the source:
--   - reading: Let λ₁ be the largest eigenvalue of Ξ and λ any other (distinct) eigenvalue; then λ₁ = 1 and λ ∈ [0, c] → 1 is an eigenvalue of Ξ, and every point of spectrum ℂ Ξ other than 1 is real and lies in [0, c]; reason: on finite-dimensional spaces the two coincide; on ℓ²(ℕⁿ)^{⊗3} the spectrum reading is the one Theorem 3.5's gap hypothesis needs
--   - encoding: orthogonal projectors Π_test → closed subspaces K with Π_test = proj K; reason: every orthogonal projector is the projector onto its closed range
--   - encoding: the fermionic Fock space ⋀ℂⁿ and the bosonic Fock space ⋁ℂⁿ → ℓ²(Fin n → Fin 2) (Jordan–Wigner, 1 = occupied, 0-based modes) and ℓ²(Fin n → ℕ); ℋ^{⊗k} is ℓ²(Fin k → ι); reason: unitarily the same spaces; Lean convention
--   - encoding: the two-copy space ⋀ℂⁿ ⊗ ⋀ℂⁿ and the two-copy operators A ⊗ B of (4.1) and Definition 5.2 → Kronecker products of the Jordan–Wigner matrices on Fin 2 → (Fin n → Fin 2) (kron2, copy 0 = first factor); reason: the paper's ⊗ is the ungraded tensor product (Lemma 5.15 decomposes ⋀ℂⁿ ⊗ ⋀ℂⁿ = ⊕ H_a ⊗ H_b; the proof of Proposition 5.5 factors ⟨Ψ|G†G|Ψ⟩ copy by copy)
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Theorem 4.2, p.29

import Definitions.Def_GaussTesting_testGf
import Definitions.Def_GaussTesting_xi

namespace GaussTesting

/-- **Theorem 4.2.** Let `λ₁` be the largest eigenvalue of `Ξ = Π^{(1,2,3)}_sym Π^{(1,2)}_test Π^{(1,2,3)}_sym`
and let `λ` be any other (distinct) eigenvalue of `Ξ`. Then `λ₁ = 1` and `λ ∈ [0, 7 / 12]`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Theorem 4.2, p.29. Here `Π_test = Π_test,G_f`, the projector onto `ker Λ` (4.2).

**Formalization Note.** `Ξ = xi (testGf n) 1` (`k = 2` test registers, `m = 3`). The eigenvalue statement is
read as: `1` is an eigenvalue of `Ξ`, and every point of the spectrum of `Ξ` other than `1` is real and
lies in `[0, 7 / 12]`; this gives `λ₁ = 1` and `λ ∈ [0, 7 / 12]`, and is how the gap `1 − 7 / 12` enters
Theorem 3.5. -/
theorem theorem_4_2 (n : ℕ) :
    (∃ v, v ≠ 0 ∧ xi (testGf n) 1 v = v) ∧
      ∀ z ∈ spectrum ℂ (xi (testGf n) 1), z = 1 ∨ (z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 7 / 12) := by sorry

end GaussTesting
