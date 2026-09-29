-- Prove2me | Theorems.Thm_Module_Flat_of_flat_of_faithfullyFlat_right
-- name    : Module.Flat.of_flat_of_faithfullyFlat_right
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/db52c433-927a-5bf5-a646-744724f3fa65
-- title:
--   Flatness descends along a faithfully flat ring extension
-- statement:
--   Let $R$, $S$ and $T$ be commutative rings equipped with algebra structures $R \to S$, $S \to T$ and $R \to T$ that form a scalar tower, so that the $R$-action on $T$ is the one obtained from $R \to S$ followed by $S \to T$. Assume that $T$ is faithfully flat as an $S$-module and flat as an $R$-module. The conclusion is that $S$ is flat as an $R$-module. Here flatness and faithful flatness are the Mathlib notions `Module.Flat` and `Module.FaithfullyFlat`: the former says that tensoring with the module preserves injectivity of linear maps (equivalently, that the functor is exact), and the latter adds the reflection property that $T \otimes_S -$ turns a map into an injective map only if it was already injective. No finiteness, surjectivity or Noetherian hypothesis is imposed on any of the three rings or on the two algebra maps.
--
--   This is the ring-theoretic form of the statement that flatness descends along a faithfully flat base change, equivalently that flatness is local on the source for the fpqc topology. It is used in the scheme-theoretic descent statement [`AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective`](thm.html#AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_of_flat_of_faithfullyFlat_right.lean

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

theorem Module.Flat.of_flat_of_faithfullyFlat_right (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by sorry
