-- Prove2me | Theorems.Thm_NumberField_denseRange_specialLinearGroup_map_finiteAdeleRing
-- name    : NumberField.denseRange_specialLinearGroup_map_finiteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/09b1b68b-7b42-5414-934c-a2b14763decc
-- title:
--   Strong approximation: SL₂(F) dense in SL₂(A_F^f)
-- statement:
--   Let $F$ be a field of characteristic zero which is a number field (a finite extension of $\mathbb{Q}$), with ring of integers $\mathcal{O}_F$, and let $\mathbb{A}_F^f =$ `FiniteAdeleRing (𝓞 F) F` be its finite adèle ring, i.e. the restricted product of the completions of $F$ at the non-zero prime ideals of $\mathcal{O}_F$ with respect to their valuation rings, carrying the restricted-product topology. The structural algebra map $F \to \mathbb{A}_F^f$ (the diagonal embedding) induces, by `Matrix.SpecialLinearGroup.map` at $n = \mathrm{Fin}\ 2$, a group homomorphism $\mathrm{SL}_2(F) \to \mathrm{SL}_2(\mathbb{A}_F^f)$ acting entrywise on $2 \times 2$ matrices of determinant $1$. The assertion is that this homomorphism has dense range: the closure of the image of $\mathrm{SL}_2(F)$ is all of $\mathrm{SL}_2(\mathbb{A}_F^f)$, the latter being topologised as a subspace of the space of $2 \times 2$ matrices over $\mathbb{A}_F^f$. There are no hypotheses beyond $F$ being a number field. Nothing is asserted about the full adèle ring (where $F$ is discrete), nor about $\mathrm{GL}_2$ or any other group.
--
--   This is the strong approximation theorem for $\mathrm{SL}_2$ over a number field, in the form: the rational points are dense in the finite-adelic points. It is used in the Langlands–Tunnell part of the development, in the construction of a Casimir eigenvector of minimal weight inside a continuous automorphic realisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_denseRange_specialLinearGroup_map_finiteAdeleRing.lean

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Group.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField

theorem NumberField.denseRange_specialLinearGroup_map_finiteAdeleRing
    (F : Type) [Field F] [NumberField F] :
    DenseRange (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap F (FiniteAdeleRing (𝓞 F) F))) := by sorry
