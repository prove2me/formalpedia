-- Prove2me | Theorems.Thm_ImplicitCalculus_bijective_tangent_map_of_injective_on_regular_levels
-- name    : ImplicitCalculus.bijective_tangent_map_of_injective_on_regular_levels
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:09:47.589648+00:00
-- url     : https://prove2.me/theorems/626fc98f-d06e-452e-ace3-a36432de45af
-- title:
--   Injective tangent differentials between regular levels are bijective
-- statement:
--   Let F and G be maps from real n-space to real c-space, with F smooth and G differentiable. Let a differentiable map f carry the zero level of F into the zero level of G. At a point y of the source level, assume DF at y and DG at f(y) are surjective. If Df at y is injective on ker DF at y, it maps that kernel bijectively onto ker DG at f(y). The source and target tangent spaces have the same dimension by rank-nullity; no global injectivity or surjectivity of f is required.
-- source:
--   General regular-level differential lemma: implicit function theorem and rank-nullity. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Implicit.lean and LinearAlgebra/FiniteDimensional/Lemmas.lean (injective_iff_surjective_of_finrank_eq_finrank). Used in Geiges, Contact Geometry, https://arxiv.org/pdf/math/0307242, Definition 2.5 and Remark 2.21(1).

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_ImplicitCalculus_tangent_map_of_mapsTo_regular_level
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open GrayStability
open scoped ContDiff Topology

theorem ImplicitCalculus.bijective_tangent_map_of_injective_on_regular_levels {n c : ℕ} (F G : E n → E c)
    (hF : ContDiff ℝ ∞ F) (hG : Differentiable ℝ G)
    (f : E n → E n) (hf : Differentiable ℝ f)
    (hmap : Set.MapsTo f (levelSet F) (levelSet G))
    (y : E n) (hy : y ∈ levelSet F)
    (hDy : Function.Surjective (fderiv ℝ F y))
    (hDfy : Function.Surjective (fderiv ℝ G (f y)))
    (hinj : Set.InjOn (fderiv ℝ f y) (tangentSpace F y)) :
    Set.BijOn (fderiv ℝ f y) (tangentSpace F y) (tangentSpace G (f y)) := by sorry
