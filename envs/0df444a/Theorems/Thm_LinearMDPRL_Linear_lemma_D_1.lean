-- Prove2me | Theorems.Thm_LinearMDPRL_Linear_lemma_D_1
-- name    : LinearMDPRL.Linear.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:55.231981+00:00
-- url     : https://prove2.me/theorems/366d8494-6498-4e54-a986-4216bf8debe7
-- title:
--   Lemma D.1, p. 26 — Σ_{i≤t} φ_i^⊤ Λ_t^{-1} φ_i ≤ d for Λ_t = λI + Σ_{i≤t} φ_i φ_i^⊤, λ > 0
-- statement:
--   Let $\lambda>0$, let $\phi_1,\dots,\phi_t\in\mathbb R^d$, and let $\Lambda_t=\lambda I+\sum_{i=1}^t\phi_i\phi_i^\top$. Then
--   $$
--   \sum_{i=1}^t\phi_i^\top(\Lambda_t)^{-1}\phi_i\le d.
--   $$
--
--   This trace bound controls the self-normalized size of the regression data and is used to bound the weights of Algorithm 1 (Lemma B.2).
-- source:
--   Jin, Yang, Wang, Jordan, arXiv:1907.05388v2, Lemma D.1, p. 26

import Mathlib

namespace LinearMDPRL.Linear

open Matrix

/-- **Lemma D.1** (arXiv:1907.05388v2, p. 26). Let `Λ_t = λI + Σ_{i=1}^t φ_i φ_i^⊤` with
`φ_i ∈ ℝ^d` and `λ > 0`. Then `Σ_{i=1}^t φ_i^⊤ (Λ_t)^{-1} φ_i ≤ d`. -/
theorem lemma_D_1 (d t : ℕ) (lam : ℝ) (hlam : 0 < lam) (φ : ℕ → Fin d → ℝ) :
    ∑ i ∈ Finset.Icc 1 t,
        φ i ⬝ᵥ ((lam • (1 : Matrix (Fin d) (Fin d) ℝ) +
          ∑ j ∈ Finset.Icc 1 t, vecMulVec (φ j) (φ j))⁻¹ *ᵥ φ i) ≤ d := by sorry

end LinearMDPRL.Linear
