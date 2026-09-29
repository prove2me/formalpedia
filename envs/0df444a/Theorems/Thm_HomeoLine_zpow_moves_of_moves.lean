-- Prove2me | Theorems.Thm_HomeoLine_zpow_moves_of_moves
-- name    : HomeoLine.zpow_moves_of_moves
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-13T07:40:08.001056+00:00
-- url     : https://prove2.me/theorems/9557ed4c-8db6-4eda-8558-6fddf2e8733d
-- title:
--   An increasing homeomorphism of the line has no non-fixed periodic point
-- statement:
--   Let $f$ be an order isomorphism of $\mathbb{R}$ — a strictly increasing bijection — and let $x$ be a point that $f$ moves, $f(x) \neq x$. Then no nonzero power of $f$ fixes $x$:
--
--   $$\forall m \in \mathbb{Z},\ m \neq 0 \implies f^{m}(x) \neq x .$$
--
--   Equivalently: on the line, a periodic point of an increasing homeomorphism is already a fixed point. The reason is monotonicity — if $f(x) > x$ then applying the increasing map $f^{k}$ to that inequality gives $f^{k+1}(x) > f^{k}(x)$, so the forward orbit is strictly increasing and never returns; the case $f(x) < x$ is symmetric, and negative exponents follow by applying $f^{-m}$.
--
--   **Role.** The standard way to turn "this map moves a point" into "this element has infinite order", which is what makes a subgroup of $\mathrm{Homeo}_+(\mathbb{R})$ torsion-free and what lets an injective $\mathbb{Z}^{2}$ be read off from two commuting maps with disjoint moved sets.
--
--   **Formalization note.** `f ^ m` is the integer power in the group of order isomorphisms, whose multiplication is composition. No continuity or piecewise-linearity is used; monotonicity is the whole content.
-- source:
--   Standard; the statement is the one-dimensional case of the fact that an increasing self-map of a linearly ordered set has no non-trivial periodic points. Used implicitly throughout M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, for instance at p. 487 where torsion-freeness of PLF(R) is recorded, and on p. 495 where the conjugates of a moved point are used to build a free abelian subgroup. PROVENANCE: not stated as a numbered result there.

import Mathlib

namespace HomeoLine

theorem zpow_moves_of_moves {f : ℝ ≃o ℝ} {x : ℝ} (hx : f x ≠ x) :
    ∀ m : ℤ, m ≠ 0 → (f ^ m) x ≠ x := by
  sorry

end HomeoLine
