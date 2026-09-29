-- Prove2me | Theorems.Thm_IrreducibleSpace_genericPoint_mem_range_of_denseRange
-- name    : IrreducibleSpace.genericPoint_mem_range_of_denseRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/b7c0bdf3-6dd4-5ca8-ace8-43355445ec66
-- title:
--   Dense continuous image from a noetherian space contains the generic point
-- statement:
--   Let $X$ and $Y$ be topological spaces, with $X$ noetherian (every open subset is compact, equivalently the closed subsets satisfy the descending chain condition) and quasi-sober (every irreducible closed subset has a generic point), and with $Y$ quasi-sober, irreducible and $T_0$; since $Y$ is irreducible and quasi-sober with $T_0$ separation, it has a unique generic point $\eta_Y =$ `genericPoint Y`, whose closure is all of $Y$. Let $f \colon X \to Y$ be a map which is continuous and has dense range, i.e. $\overline{f(X)} = Y$. The conclusion is that $\eta_Y$ lies in the range of $f$: there is a point $x \in X$ with $f(x) = \eta_Y$. Thus a dense continuous image of a noetherian quasi-sober space in an irreducible sober space actually hits the generic point, not merely a dense set of points.
--
--   This is the point-set topology step which upgrades density of an image to the generic point being attained; noetherianity of $X$ is what makes it true (for a non-noetherian source, the closed points of an affine line over an infinite field form a dense image missing the generic point). It is used in the scheme-theoretic lemma [`AlgebraicGeometry.Scheme.Hom.mem_range_of_specializes_of_mem_closure`](thm.html#AlgebraicGeometry.Scheme.Hom.mem_range_of_specializes_of_mem_closure), where membership of a point in the closure of the image of a morphism is converted into membership in the image.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IrreducibleSpace_genericPoint_mem_range_of_denseRange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem IrreducibleSpace.genericPoint_mem_range_of_denseRange
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [QuasiSober X] [QuasiSober Y] [IrreducibleSpace Y] [T0Space Y]
    {f : X → Y} (hf : Continuous f) (hd : DenseRange f) :
    genericPoint Y ∈ Set.range f := by sorry
