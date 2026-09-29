-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
-- name    : NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6bf3600a-619b-531a-9c00-d691e21ade59
-- title:
--   The infinite adele ring is homeomorphic to the mixed space
-- statement:
--   Let $K$ be a field, so that its infinite places, their completions and the associated mixed space are defined. The infinite adele ring $\mathbb{A}_{K,\infty}=\prod_{v\mid\infty}K_v$ carries the product topology of the completions $K_v$ at the infinite places $v$ of $K$, and the mixed space is $(\{v \text{ real}\}\to\mathbb{R})\times(\{v\text{ complex}\}\to\mathbb{C})$ with the product topology. The map `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K` is the canonical ring isomorphism between them, whose components are the identifications $K_v\cong\mathbb{R}$ for $v$ real and $K_v\cong\mathbb{C}$ for $v$ complex obtained by extending to the completion an embedding of $K$ defining $v$. The assertion is that this ring isomorphism, viewed as a map of topological spaces, satisfies `IsHomeomorph`: it is continuous, it is an open map, and it is bijective. Thus the algebraic identification of $\mathbb{A}_{K,\infty}$ with $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ (for a number field $K$) is simultaneously an identification of topological spaces.
--
--   This is the topological half of the Minkowski-theoretic identification $K\otimes_{\mathbb Q}\mathbb R\cong\mathbb R^{r_1}\times\mathbb C^{r_2}$, which licenses the transfer of continuity, compactness and smoothness statements between the infinite adele ring and the mixed space. It is used in the analytic work on automorphic forms, where test functions and integrals over the archimedean component are constructed on $\mathbb R^{r_1}\times\mathbb C^{r_2}$ and transported back.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace.lean

import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace
    (K : Type) [Field K] :
    IsHomeomorph (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by sorry
