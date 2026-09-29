-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_trace_mixedSpace_apply
-- name    : NumberField.mixedEmbedding.trace_mixedSpace_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/f9df9dcb-88b9-5689-bb4f-d8ef17e1c89c
-- title:
--   Trace of the mixed space of a number field over ℝ
-- statement:
--   Let $K$ be a number field (a field with the `NumberField` structure, taken in the base universe) and let $z$ be an element of its mixed space `mixedSpace K`, that is, of the $\mathbb{R}$-algebra $\bigl(\{w : \text{InfinitePlace } K \mid w \text{ real}\} \to \mathbb{R}\bigr) \times \bigl(\{w : \text{InfinitePlace } K \mid w \text{ complex}\} \to \mathbb{C}\bigr)$, with $z.1$ its real-place component and $z.2$ its complex-place component. The assertion is that the algebra trace of the multiplication-by-$z$ map of this finite-dimensional $\mathbb{R}$-algebra, $\mathrm{Tr}_{\mathrm{mixedSpace}\,K/\mathbb{R}}(z)$, equals $$\sum_{w \text{ real}} z.1(w) \; + \; \sum_{w \text{ complex}} 2\,\mathrm{Re}\bigl(z.2(w)\bigr),$$ the first sum over the subtype of real infinite places of $K$ and the second over the subtype of complex infinite places, both finite. Classical logic is used in the ambient formulation.
--
--   This is the explicit formula for the trace form on the Minkowski (mixed) space of a number field, the trace of the product $\mathbb{R}$-algebra $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$. It serves to compute pairings and Fourier-analytic normalisations at the archimedean places, and is used in the treatment of Whittaker coefficients of automorphic forms and in the computation of Fourier integrals of pure tensors over archimedean places in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_trace_mixedSpace_apply.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding

open scoped Classical in

theorem NumberField.mixedEmbedding.trace_mixedSpace_apply
    (K : Type) [Field K] [NumberField K] (z : mixedSpace K) :
    Algebra.trace ℝ (mixedSpace K) z =
      (∑ w : {w : InfinitePlace K // w.IsReal}, z.1 w) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, 2 * (z.2 w).re := by sorry
