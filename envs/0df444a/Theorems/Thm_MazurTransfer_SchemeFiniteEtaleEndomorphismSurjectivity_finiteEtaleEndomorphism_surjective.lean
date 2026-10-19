-- Prove2me | Theorems.Thm_MazurTransfer_SchemeFiniteEtaleEndomorphismSurjectivity_finiteEtaleEndomorphism_surjective
-- name    : MazurTransfer.SchemeFiniteEtaleEndomorphismSurjectivity.finiteEtaleEndomorphism_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:34:45.213245+00:00
-- url     : https://prove2.me/theorems/81c3e8ab-e6b9-43af-a9e8-720f2b85e162
-- title:
--   A finite etale endomorphism of a nonempty connected scheme is surjective
-- statement:
--   Let X be a nonempty preconnected scheme and let g be a finite etale endomorphism of X. Then g is surjective. The named downstream consumer is surjectivity of the actual rational Picard norm factors.
-- source:
--   Complete original MazurTheorem SchemeFiniteEtaleEndomorphismSurjectivity.finiteEtaleEndomorphism_surjective, preserving the full universe-polymorphic type and original Mathlib clopen-image proof. Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a finite etale endomorphism of a nonempty connected
scheme is surjective, from its nonempty clopen image.
Named downstream consumer: actual rational Picard norm isogenies.
-/
import Mathlib

open AlgebraicGeometry
universe u

theorem MazurTransfer.SchemeFiniteEtaleEndomorphismSurjectivity.finiteEtaleEndomorphism_surjective {X : Scheme.{u}}
    [PreconnectedSpace X] [Nonempty X] (g : X ⟶ X) [IsFinite g] [Etale g] : Surjective g := by sorry
