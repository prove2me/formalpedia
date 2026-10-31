-- Prove2me | Theorems.Thm_HiddenConvexSO_theorem_8
-- name    : HiddenConvexSO.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:27.100036+00:00
-- url     : https://prove2.me/theorems/36f231ec-cc6d-4e46-b29e-90b8224e9845
-- title:
--   Theorem 8 — every $X\in\mathrm{SO}(n)$ is $\mathrm{SO}(n)$-conjugate into the maximal torus
-- statement:
--   For every $n$ and every $X\in\mathrm{SO}(n)$ there exist $U\in\mathrm{SO}(n)$ and angles $\theta_1,\dots,\theta_k\in[0,2\pi)$, $k=\lfloor n/2\rfloor$, such that
--
--   $$
--   U^\top X U = R(\theta_1,\dots,\theta_k),
--   $$
--
--   where $R(\theta_1,\dots,\theta_k)$ is the block rotation matrix of displays (7)–(8). In other words, $U^\top XU$ lies in the maximal torus $\mathbb T$.
--
--   This is the real normal form of a rotation (a special case of the maximal torus theorem). The paper uses it to write two rotations as elements of a torus when building loops in Lemma 4.
--
--   **Formalization Note** $\mathrm{SO}(n)$ is `Matrix.specialOrthogonalGroup (Fin n) ℝ`; the conjugator $U$ is required to lie in $\mathrm{SO}(n)$, not only in $\mathrm{O}(n)$; $R(\theta)$ is `torusMat n θ` with `θ : Fin (n / 2) → ℝ`, each `θ i ∈ Set.Ico 0 (2π)`. No condition on $n$.
--
--   Differences from the source:
--   - encoding: SO(n) = {X ∈ ℝ^{n×n} : XᵀX = I, det X = 1} with the subspace topology (p.1, p.13) → Matrix.specialOrthogonalGroup (Fin n) ℝ (star A * A = 1 ∧ A * star A = 1 ∧ det A = 1), coerced subtype topology; 0-based indices; reason: Lean convention; for real square matrices AᵀA = I already gives AAᵀ = I, so the same set
--   - encoding: R(θ₁, …, θ_k) with 1-based blocks in rows 2i−1, 2i → torusMat n θ, θ : Fin (n / 2) → ℝ, block b in rows 2b, 2b+1, trailing 1 at index n−1; reason: 0-based indexing; the same matrix
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, Theorem 8, p.9

import Mathlib
import Definitions.Def_HiddenConvexSO_torusMat

namespace HiddenConvexSO

/-- **Theorem 8 (maximal torus theorem for SO(n)).**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, Theorem 8, p.9 (PDF p.9): "For any X ∈ SO(n), there
exists U ∈ SO(n) so that U⊺XU ∈ T. That is, U⊺XU = R(θ1, . . . , θk) for some θi ∈ [0, 2π)."

**Formalization Note.** SO(n) is `Matrix.specialOrthogonalGroup (Fin n) ℝ`; the conjugator `U` is in
SO(n), not merely O(n). `R(θ₁, …, θ_k)` is `torusMat n θ` with `θ : Fin (n / 2) → ℝ`, `k = ⌊n/2⌋`,
and each angle lies in `[0, 2π)` (`Set.Ico 0 (2π)`). No restriction on `n`. -/
theorem theorem_8 (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    ∃ U ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ, ∃ θ : Fin (n / 2) → ℝ,
      (∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) ∧ U.transpose * X * U = torusMat n θ := by sorry

end HiddenConvexSO
