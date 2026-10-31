-- Prove2me | Theorems.Thm_HiddenConvexSO_convex_iff_line_sections
-- name    : HiddenConvexSO.convex_iff_line_sections
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:34.188226+00:00
-- url     : https://prove2.me/theorems/303b3c32-2c9f-47a8-a7d1-4ae785fbf84d
-- title:
--   A subset of $\mathbb R^2$ is convex iff its intersection with every line is connected
-- statement:
--   A set $S\subseteq\mathbb R^2$ is convex if and only if its intersection with every one-dimensional affine subspace is connected. Writing the lines as $\{z:\langle\ell,z\rangle=\alpha\}$ with $\ell\in\mathbb R^2\setminus\{0\}$ and $\alpha\in\mathbb R$:
--
--   $$
--   S \text{ convex}\iff \forall\,\ell\in\mathbb R^2\setminus\{0\},\ \forall\,\alpha\in\mathbb R:\quad S\cap\{z\in\mathbb R^2:\ \ell_1z_1+\ell_2z_2=\alpha\}\ \text{is connected}.
--   $$
--
--   Connectedness is in the paper's sense, under which the empty set is connected. This observation turns Theorem 3 into Corollary 1: a line section of $\pi(\mathrm{SO}(n))$ is the linear image of a hyperplane section of $\mathrm{SO}(n)$.
--
--   **Formalization Note** $\mathbb R^2$ is `ℝ × ℝ`; connectedness is `IsPreconnected`. Both directions are stated.
--
--   Differences from the source:
--   - reading: connected → IsPreconnected (the empty set counts as connected); reason: the paper defines connectedness in the proof of Theorem 3 (p.16): not connected means there are nonempty disjoint closed U, V covering the set; under this definition the empty set is connected
--   - encoding: one-dimensional affine subspaces of ℝ² → {z : ℝ × ℝ | ℓ.1 * z.1 + ℓ.2 * z.2 = α} with ℓ ≠ 0, α ∈ ℝ; reason: every line in ℝ² is of this form and every such set is a line; the paper parametrizes lines this way in the proof of Corollary 1
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, §4, p.12 ("a subset of R2 is convex if and only if its intersection with every one-dimensional affine subspace is connected"; also p.5); line parametrization from the proof of Corollary 1, p.12

import Mathlib

namespace HiddenConvexSO

/-- **A planar set is convex iff every line section is connected.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, §4, p.12 (PDF p.12; also p.5): "the observation that
a subset of R2 is convex if and only if its intersection with every one-dimensional affine subspace
is connected."

**Formalization Note.** `ℝ²` is `ℝ × ℝ`. The one-dimensional affine subspaces of `ℝ²` are written as
in the proof of Corollary 1 (p.12): `{z : ⟨ℓ, z⟩ = α}` with `ℓ ∈ ℝ² ∖ {0}` and `α ∈ ℝ`; every line has
this form. "Connected" is `IsPreconnected` (the paper's definition, p.16), so an empty section counts
as connected; with nonempty-connectedness the forward direction would fail for any convex set missing
a line. Both directions are stated. -/
theorem convex_iff_line_sections (S : Set (ℝ × ℝ)) :
    Convex ℝ S ↔
      ∀ ℓ : ℝ × ℝ, ℓ ≠ 0 → ∀ α : ℝ,
        IsPreconnected (S ∩ {z : ℝ × ℝ | ℓ.1 * z.1 + ℓ.2 * z.2 = α}) := by sorry

end HiddenConvexSO
