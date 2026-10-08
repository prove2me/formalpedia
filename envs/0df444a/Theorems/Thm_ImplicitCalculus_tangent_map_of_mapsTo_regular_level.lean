-- Prove2me | Theorems.Thm_ImplicitCalculus_tangent_map_of_mapsTo_regular_level
-- name    : ImplicitCalculus.tangent_map_of_mapsTo_regular_level
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:45:34.776327+00:00
-- url     : https://prove2.me/theorems/d4edc4bd-867d-44f9-8209-6507e3e712a3
-- title:
--   Differential of a local regular-level preserving map preserves tangents
-- statement:
--   Let V be a real Banach space, W a finite-dimensional real normed space, and U and Z real normed spaces. Suppose F:V→W is strictly differentiable at y, with surjective derivative D, and v lies in ker D. Let g:V→U be differentiable at y and H:U→Z differentiable at g(y). Suppose that for every z in some neighborhood of y, F(z)=F(y) implies H(g(z))=H(g(y)). Then
--
--   $$ DH(g(y))\bigl(Dg(y)[v]\bigr)=0. $$
--
--   Thus a map locally preserving a regular level carries its tangent vectors into the target level kernel. No regularity or nondegeneracy of the target level is needed. Strict differentiability and finite-dimensional codomain of F are sufficient for the implicit-function construction.
-- source:
--   Implicit-function-theorem tangent characterization; application to tangent preservation in Gray stability (Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, Theorem 2.20). The proof uses Mathlib.Analysis.Calculus.Implicit.HasStrictFDerivAt.implicitFunction, map_implicitFunction_eq and to_implicitFunction at commit 0df444a360eaa60ab8c11dca51a86af692955474. This local Banach-space formulation is an independent generalization, not a quoted theorem statement from Geiges.

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Real.Basic

open Set Filter
open scoped Topology
set_option autoImplicit false

theorem ImplicitCalculus.tangent_map_of_mapsTo_regular_level {V W U Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : V → W) (D : V →L[ℝ] W) (y v : V)
    (hF : HasStrictFDerivAt F D y) (hD : Function.Surjective D) (hv : D v = 0)
    (g : V → U) (H : U → Z) (hg : DifferentiableAt ℝ g y)
    (hH : DifferentiableAt ℝ H (g y))
    (hmap : ∀ᶠ z in 𝓝 y, F z = F y → H (g z) = H (g y)) :
    fderiv ℝ H (g y) (fderiv ℝ g y v) = 0 := by sorry
