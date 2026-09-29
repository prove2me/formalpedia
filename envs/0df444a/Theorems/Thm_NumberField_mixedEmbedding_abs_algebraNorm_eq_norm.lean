-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_abs_algebraNorm_eq_norm
-- name    : NumberField.mixedEmbedding.abs_algebraNorm_eq_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/03e6e9e1-25cd-5ee2-9ab2-c78c8f67ff75
-- title:
--   Absolute algebra norm on the mixed space equals `mixedEmbedding.norm`
-- statement:
--   Let $K$ be a number field (a field with the number-field instance) and let $x$ be an element of the mixed space $\mathbb{R}^{\{w \text{ real}\}} \times \mathbb{C}^{\{w \text{ complex}\}}$ attached to $K$, that is, of `NumberField.mixedEmbedding.mixedSpace K`, the product of copies of $\mathbb{R}$ indexed by the real infinite places of $K$ with copies of $\mathbb{C}$ indexed by the complex infinite places, regarded as a commutative $\mathbb{R}$-algebra. The assertion is that the absolute value of the algebra norm $N_{K_\infty/\mathbb{R}}(x)$, i.e. the determinant of the $\mathbb{R}$-linear multiplication map $y \mapsto xy$ on the mixed space, coincides with $\mathrm{norm}(x) = \prod_{w \mid \infty} \lVert x \rVert_w^{\,\mathrm{mult}(w)}$, where the product runs over all infinite places $w$ of $K$, $\lVert x \rVert_w$ is the ordinary absolute value of the real coordinate $x_w$ when $w$ is real and the complex absolute value of the coordinate $x_w$ when $w$ is complex, and $\mathrm{mult}(w)$ is $1$ for real $w$ and $2$ for complex $w$. Both sides are real numbers, and the identity holds for every $x$, with no invertibility hypothesis.
--
--   This is the classical product formula for the archimedean norm, $|N_{K/\mathbb{Q}}(\alpha)| = \prod_{w \mid \infty} |\alpha|_w^{[K_w : \mathbb{R}]}$, extended from the image of $K$ to the whole archimedean algebra $K_\infty$; equivalently it identifies the modulus of multiplication by $x$ on $K_\infty$ with the product of the local moduli. It is used in the computation of archimedean integrals against Haar measure on the infinite adeles, where the determinantal density must be rewritten through the place-by-place absolute values.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_abs_algebraNorm_eq_norm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.mixedEmbedding.abs_algebraNorm_eq_norm
    (K : Type) [Field K] [NumberField K] (x : mixedEmbedding.mixedSpace K) :
    |Algebra.norm ℝ x| = mixedEmbedding.norm x := by sorry
