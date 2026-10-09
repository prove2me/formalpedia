-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lemma_D_1
-- name    : LinearMDPRL.Misspec.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:44.490052+00:00
-- url     : https://prove2.me/theorems/c41105a7-fa4d-4119-86d1-1e4a64134e82
-- title:
--   Lemma D.1, p. 26 — Σ_{i=1}^t φ_i^⊤(Λ_t)^{-1}φ_i ≤ d for Λ_t = λI + Σφ_iφ_i^⊤
-- statement:
--   Let $\lambda>0$, let $\phi_1,\dots,\phi_t\in\mathbb R^d$, and let $\Lambda_t=\lambda I+\sum_{i=1}^t\phi_i\phi_i^\top$. Then
--   $$\sum_{i=1}^t\phi_i^\top(\Lambda_t)^{-1}\phi_i\le d.$$
--
--   A deterministic trace inequality for regularized Gram matrices; it is the last step of the proof of Lemma C.4.
--
--   **Formalization Note** The vectors are a sequence indexed by $\mathbb N$, of which $\phi_1,\dots,\phi_t$ are used. The same lemma is drafted in the companion mission on Theorem 3.1; it is restated here because draft items cannot import each other.
-- source:
--   arXiv:1907.05388v2, Lemma D.1, p. 26

import Mathlib

open Matrix

namespace LinearMDPRL.Misspec

/-- **Lemma D.1** (p. 26). Let `Λ_t = λI + Σ_{i=1}^t φ_i φ_i^⊤` with `φ_i ∈ ℝ^d` and `λ > 0`. Then
`Σ_{i=1}^t φ_i^⊤ (Λ_t)^{-1} φ_i ≤ d`. -/
theorem lemma_D_1 {d : ℕ} (lam : ℝ) (hlam : 0 < lam) (t : ℕ) (φ : ℕ → Fin d → ℝ) :
    ∑ i ∈ Finset.Icc 1 t,
        φ i ⬝ᵥ (lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
          ∑ j ∈ Finset.Icc 1 t, vecMulVec (φ j) (φ j))⁻¹ *ᵥ φ i ≤ d := by sorry

end LinearMDPRL.Misspec
