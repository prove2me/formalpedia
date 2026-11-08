-- Prove2me | Theorems.Thm_GaussianSweep_lemma_8_10
-- name    : GaussianSweep.lemma_8_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:07.971371+00:00
-- url     : https://prove2.me/theorems/b223af09-9b96-4325-b445-d682ff7be2e4
-- title:
--   Lemma 8.10 — angles of three unit vectors: determinant and (semi)definiteness
-- statement:
--   Let $\alpha, \beta, \gamma \in [0, \pi]$ and let $C$ be the symmetric $3 \times 3$ matrix with unit diagonal and off-diagonal entries $C_{23} = \cos\alpha$, $C_{13} = \cos\beta$, $C_{12} = \cos\gamma$. Then
--   $$
--   \det C = \big(\cos\alpha - \cos(\beta+\gamma)\big)\big(\cos(\beta-\gamma) - \cos\alpha\big). \tag{8.5}
--   $$
--   Moreover, $C$ is positive semidefinite if and only if
--   $$
--   \alpha \le \beta + \gamma, \quad \beta \le \alpha + \gamma, \quad \gamma \le \alpha + \beta, \quad \alpha + \beta + \gamma \le 2\pi,
--   $$
--   and positive definite if and only if these four inequalities are strict. This describes exactly which triples of angles are realized by three unit vectors.
--
--   **Formalization Note** The matrix is written out with 0-based indices: $C_{12}, C_{13}, C_{23}$ are the entries $(0,1), (0,2), (1,2)$.
--
--   Differences from the source:
--   - encoding: entries C₁₂, C₁₃, C₂₃ → entries (0,1), (0,2), (1,2) of a Fin 3 matrix; reason: 0-based indexing; same matrix
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.10, Eq. (8.5), p.51 (PDF p.53)

import Mathlib

namespace GaussianSweep

/-- Lemma 8.10 (angles of three unit vectors) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.10, Eq. (8.5), p.51 (PDF p.53)).
Let `α, β, γ ∈ [0, π]` and `C` the symmetric `3 × 3` matrix with unit diagonal and `C₂₃ = cos α`,
`C₁₃ = cos β`, `C₁₂ = cos γ`. Then `det C = (cos α − cos(β + γ))(cos(β − γ) − cos α)`; `C` is
positive semidefinite iff `α ≤ β + γ`, `β ≤ α + γ`, `γ ≤ α + β` and `α + β + γ ≤ 2π`; and
positive definite iff these four inequalities are strict.

**Formalization Note** 0-based indices: `C₁₂, C₁₃, C₂₃` are `C 0 1, C 0 2, C 1 2`. -/
theorem lemma_8_10 (α β γ : ℝ) (hα : α ∈ Set.Icc 0 Real.pi) (hβ : β ∈ Set.Icc 0 Real.pi)
    (hγ : γ ∈ Set.Icc 0 Real.pi) :
    let C : Matrix (Fin 3) (Fin 3) ℝ :=
      !![1, Real.cos γ, Real.cos β; Real.cos γ, 1, Real.cos α; Real.cos β, Real.cos α, 1]
    C.det = (Real.cos α - Real.cos (β + γ)) * (Real.cos (β - γ) - Real.cos α) ∧
    (C.PosSemidef ↔ α ≤ β + γ ∧ β ≤ α + γ ∧ γ ≤ α + β ∧ α + β + γ ≤ 2 * Real.pi) ∧
    (C.PosDef ↔ α < β + γ ∧ β < α + γ ∧ γ < α + β ∧ α + β + γ < 2 * Real.pi) := by sorry

end GaussianSweep
