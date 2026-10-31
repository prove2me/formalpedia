-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_10
-- name    : LinearZeroSumMG.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:51:22.886169+00:00
-- url     : https://prove2.me/theorems/7b73fd1d-5d50-495e-808a-4e51ade8a122
-- title:
--   Lemma 10, p.29 — elliptical potential: $\log\frac{\det\Lambda_t}{\det\Lambda_0}\le\sum_j\phi_j^\top\Lambda_{j-1}^{-1}\phi_j\le2\log\frac{\det\Lambda_t}{\det\Lambda_0}$
-- statement:
--   **Lemma 10 (Elliptical potential lemma).** Let $(\phi_t)_{t\ge0}$ be vectors in $\mathbb R^d$ with $\|\phi_t\|\le1$, let $\Lambda_0$ be a positive definite matrix whose smallest eigenvalue is at least $1$, and let $\Lambda_t=\Lambda_0+\sum_{i=1}^t\phi_i\phi_i^\top$. Then for every $t$,
--   $$
--   \log\frac{\det\Lambda_t}{\det\Lambda_0}\le\sum_{j=1}^t\phi_j^\top\Lambda_{j-1}^{-1}\phi_j\le2\log\frac{\det\Lambda_t}{\det\Lambda_0}.
--   $$
--
--   The upper half bounds the sum of squared bonuses in the final step of the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: λ_min(Λ₀) ≥ 1 → vᵀΛ₀v ≥ ‖v‖² for all v (with Λ₀ positive definite); reason: equivalent for a symmetric matrix
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 10, p.29

import Mathlib
import Definitions.Def_LinearZeroSumMG_clip

open Matrix

namespace LinearZeroSumMG

/-- **Lemma 10 (Elliptical Potential Lemma).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 10, p.29: "Suppose that
`{φ_t}_{t≥0}` is a sequence in `ℝ^d` satisfying `‖φ_t‖ ≤ 1, ∀t`. Let `Λ₀ ∈ ℝ^{d×d}` be a positive
definite matrix, and `Λ_t = Λ₀ + ∑_{i∈[t]} φ_iφ_iᵀ`. If the smallest eigenvalue of `Λ₀` satisfies
`λ_min(Λ₀) ≥ 1`, then
`log(det Λ_t / det Λ₀) ≤ ∑_{j∈[t]} φ_jᵀΛ_{j−1}⁻¹φ_j ≤ 2 log(det Λ_t / det Λ₀), ∀t`."

**Formalization Note** `λ_min(Λ₀) ≥ 1` is written as `vᵀΛ₀v ≥ ‖v‖²` for every `v` (for the symmetric
positive definite `Λ₀` these are equivalent). `[t] = {1, …, t}`; `log` is `Real.log`. -/
theorem lemma_10 {d : ℕ} (ψ : ℕ → Fin d → ℝ) (hψ : ∀ t, ApproxVI.euclNorm (ψ t) ≤ 1)
    (Λ₀ : Matrix (Fin d) (Fin d) ℝ) (hΛ₀ : Λ₀.PosDef)
    (hmin : ∀ v : Fin d → ℝ, v ⬝ᵥ v ≤ v ⬝ᵥ Λ₀ *ᵥ v) (t : ℕ) :
    Real.log ((Λ₀ + ∑ i ∈ Finset.Icc 1 t, vecMulVec (ψ i) (ψ i)).det / Λ₀.det) ≤
        ∑ j ∈ Finset.Icc 1 t,
          ψ j ⬝ᵥ (Λ₀ + ∑ i ∈ Finset.Icc 1 (j - 1), vecMulVec (ψ i) (ψ i))⁻¹ *ᵥ ψ j ∧
      ∑ j ∈ Finset.Icc 1 t,
          ψ j ⬝ᵥ (Λ₀ + ∑ i ∈ Finset.Icc 1 (j - 1), vecMulVec (ψ i) (ψ i))⁻¹ *ᵥ ψ j ≤
        2 * Real.log ((Λ₀ + ∑ i ∈ Finset.Icc 1 t, vecMulVec (ψ i) (ψ i)).det / Λ₀.det) := by sorry

end LinearZeroSumMG
