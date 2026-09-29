-- Prove2me | Theorems.Thm_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le
-- name    : ModularGroup.exists_bounds_smul_of_mem_fd_of_im_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d2277b2e-1577-5a00-988c-3321469e1ee0
-- title:
--   Finitely many translates of a truncated fundamental domain are bounded
-- statement:
--   Let $S$ be a finite set of matrices in $\mathrm{SL}_2(\mathbb Z)$ and let $Y$ be a real number. Then there exist real numbers $B$, $y_0$, $Y_1$ with $y_0 > 0$ such that for every $\sigma \in S$, every point $z$ of the upper half-plane $\mathbb H$ lying in Mathlib's standard fundamental domain `ModularGroup.fd` (that is, $1 \le |z|^2$ and $|\operatorname{Re} z| \le 1/2$), and satisfying in addition $\operatorname{Im} z \le Y$, the image $\sigma \cdot z$ under the Möbius action of $\mathrm{SL}_2(\mathbb Z)$ on $\mathbb H$ satisfies the three inequalities $|\operatorname{Re}(\sigma \cdot z)| \le B$, $y_0 \le \operatorname{Im}(\sigma \cdot z)$ and $\operatorname{Im}(\sigma \cdot z) \le Y_1$. Equivalently, the union of the $S$-translates of the truncated domain $\{z \in \mathcal D : \operatorname{Im} z \le Y\}$ is contained in a box $\{|\operatorname{Re} w| \le B,\ y_0 \le \operatorname{Im} w \le Y_1\}$ with $y_0 > 0$. No positivity or size hypothesis is imposed on $Y$, $B$ or $Y_1$; when $S$ is empty or $Y$ is too small the conclusion holds vacuously.
--
--   This is a quantitative form of the elementary part of reduction theory for $\mathrm{SL}_2(\mathbb Z)$ acting on $\mathbb H$: finitely many translates of a truncated standard fundamental domain stay inside a compact box, bounded away from the real axis and from the cusp. It feeds the construction of a finite covering of a modular curve by coordinate boxes, being used by [`ModularGroup.exists_finset_box_or_cusp`](thm.html#ModularGroup.exists_finset_box_or_cusp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped UpperHalfPlane MatrixGroups

theorem ModularGroup.exists_bounds_smul_of_mem_fd_of_im_le (S : Finset SL(2, ℤ)) (Y : ℝ) :
    ∃ B y₀ Y₁ : ℝ, 0 < y₀ ∧ ∀ σ ∈ S, ∀ z ∈ ModularGroup.fd, z.im ≤ Y →
      |(σ • z).re| ≤ B ∧ y₀ ≤ (σ • z).im ∧ (σ • z).im ≤ Y₁ := by sorry
