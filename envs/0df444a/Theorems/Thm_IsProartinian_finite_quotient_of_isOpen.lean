-- Prove2me | Theorems.Thm_IsProartinian_finite_quotient_of_isOpen
-- name    : IsProartinian.finite_quotient_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/eb7757df-8471-59f1-875d-58ca9f273b56
-- title:
--   Open ideals of a pro-Artinian local ring have finite index
-- statement:
--   Let $R$ be a commutative ring carrying a topology making it a topological ring, and assume $R$ is local. Assume further that $R$ is pro-Artinian in the sense of the class [`IsProartinian`](def/Deformations_IsProartinian.html#L185): the topology on $R$ is a linear topology over $R$ (it admits a neighbourhood basis of $0$ consisting of ideals), $R$ is $T_0$, $R$ is complete for the uniformity coming from its additive group, and for every ideal $I$ of $R$ which is open as a subset of $R$ the quotient ring $R/I$ is Artinian. Assume finally that the residue field $\mathrm{ResidueField}\,R = R/\mathfrak m_R$ is finite. Then for every ideal $I$ of $R$ whose underlying set is open in $R$, the quotient ring $R/I$ is finite.
--
--   This is the statement that open ideals of a local pro-Artinian ring with finite residue field have finite index, i.e. the total-boundedness input for the compactness of such rings. It is used in the construction of the categories of pro-Artinian coefficient rings and their (co)representability statements, and is cited by [`Deformation.ProartinianCat.isCorepresentable_of_preservesLimits`](thm.html#Deformation.ProartinianCat.isCorepresentable_of_preservesLimits) and by several statements about Galois representations of a prescribed type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsProartinian_finite_quotient_of_isOpen.lean

import Mathlib
import Definitions.Def_Deformations_IsProartinian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem IsProartinian.finite_quotient_of_isOpen {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLocalRing R] [IsProartinian R] [Finite (IsLocalRing.ResidueField R)] (I : Ideal R) (hI : IsOpen (I : Set R)) :
  Finite (R ⧸ I) := by sorry
