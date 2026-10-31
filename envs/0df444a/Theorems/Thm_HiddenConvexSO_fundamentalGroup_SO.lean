-- Prove2me | Theorems.Thm_HiddenConvexSO_fundamentalGroup_SO
-- name    : HiddenConvexSO.fundamentalGroup_SO
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:32.874203+00:00
-- url     : https://prove2.me/theorems/c9620e7f-b93c-4f73-be79-cadcaf0db7e7
-- title:
--   $\pi_1(\mathrm{SO}(n))\cong\mathbb Z/2\mathbb Z$ for $n\ge 3$
-- statement:
--   For every $n\ge 3$, the fundamental group of the special orthogonal group is cyclic of order two:
--
--   $$
--   \pi_1\bigl(\mathrm{SO}(n),\,I\bigr)\ \cong\ \mathbb Z/2\mathbb Z .
--   $$
--
--   Here $\mathrm{SO}(n)=\{X\in\mathbb R^{n\times n}: X^\top X=I,\ \det X=1\}$ carries the subspace topology of $\mathbb R^{n\times n}$, and the base point is the identity matrix $I$.
--
--   The paper cites this fact from Hatcher. Its consequence used in Lemma 3 is that any loop in $\mathrm{SO}(n)$, concatenated with itself, is null-homotopic.
--
--   **Formalization Note** $\mathrm{SO}(n)$ is `Matrix.specialOrthogonalGroup (Fin n) ℝ` as a subtype; $\pi_1$ is Mathlib's `FundamentalGroup` at `1`; $\mathbb Z/2\mathbb Z$ is `Multiplicative (ZMod 2)`. The statement asserts that a group isomorphism exists.
--
--   Differences from the source:
--   - reading: two loops are equivalent if there is a continuous T : [0,1]² → X with T(0,·) = γ₁, T(1,·) = γ₂ (p.13, no endpoint condition) → Path.Homotopic: homotopy rel endpoints (fixed base point at every stage); reason: read literally, any two loops in a path-connected space are equivalent (T(s,t) = γ₁((1−s)t) contracts γ₁ to a point, then reverse for γ₂), which would make π₁(ℝ² ∖ 0) trivial against the paper's own claim that it is ℤ (p.13); the based homotopy is the standard definition of π₁ in the cited reference [17] and the one the proofs use
--   - encoding: SO(n) = {X ∈ ℝ^{n×n} : XᵀX = I, det X = 1} with the subspace topology (p.1, p.13) → Matrix.specialOrthogonalGroup (Fin n) ℝ (star A * A = 1 ∧ A * star A = 1 ∧ det A = 1), coerced subtype topology; 0-based indices; reason: Lean convention; for real square matrices AᵀA = I already gives AAᵀ = I, so the same set
--   - encoding: π₁(SO(n)) with no base point named → FundamentalGroup at the identity matrix 1; reason: SO(n) is path connected, so the base point does not matter (p.13)
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, §4.1, p.13 ("for n ≥ 3, the fundamental group of SO(n) is Z/2Z"), cited from Hatcher [17]

import Mathlib

namespace HiddenConvexSO

/-- **π₁(SO(n)) ≅ ℤ/2ℤ for `n ≥ 3`.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, §4.1, p.13 (PDF p.13), cited from Hatcher [17]:
"we will also need the fact that for n ≥ 3, the fundamental group of SO(n) is Z/2Z."

**Formalization Note.** `SO(n) = {X ∈ ℝ^{n×n} : XᵀX = I, det X = 1}` (p.1) is
`Matrix.specialOrthogonalGroup (Fin n) ℝ`, coerced to a type with the subspace topology of
`ℝ^{n×n}` (p.13). The base point is the identity matrix `1`; SO(n) is path connected, so the choice
does not matter (p.13). `π₁` is Mathlib's `FundamentalGroup` (homotopy rel endpoints) and `ℤ/2ℤ` is
`Multiplicative (ZMod 2)`. -/
theorem fundamentalGroup_SO (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (FundamentalGroup (Matrix.specialOrthogonalGroup (Fin n) ℝ) 1 ≃*
      Multiplicative (ZMod 2)) := by sorry

end HiddenConvexSO
