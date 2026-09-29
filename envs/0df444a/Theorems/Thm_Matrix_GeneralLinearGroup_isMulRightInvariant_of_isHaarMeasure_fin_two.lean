-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two
-- name    : Matrix.GeneralLinearGroup.isMulRightInvariant_of_isHaarMeasure_fin_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/ac44a672-7dfe-5d60-9288-7911487d803f
-- title:
--   Haar measure on GL₂(F) is right invariant
-- statement:
--   Let $F$ be a field of characteristic zero carrying a topology for which it is a topological ring, and consider the group $G = \mathrm{GL}_2(F)$ of invertible $2\times 2$ matrices over $F$ with its induced topology. Assume $G$ is locally compact and second countable, and equip it with a measurable space structure which is its Borel $\sigma$-algebra. Let $\mu$ be a measure on $G$ that is a Haar measure, that is, a left-invariant regular measure which is finite on compact sets and positive on non-empty open sets. The assertion is that $\mu$ is also right invariant: for every $g \in G$, the pushforward of $\mu$ along the map $x \mapsto xg$ equals $\mu$, so that $\mu(Eg) = \mu(E)$ for all Borel sets $E \subseteq G$. In other words, $\mathrm{GL}_2(F)$ is unimodular under these hypotheses.
--
--   This is the unimodularity of $\mathrm{GL}_2$ over a topological field, in the form 'left Haar measure is bi-invariant'. It is used in the integral manipulations of the Rankin–Selberg and cubic-induction parts of the Langlands–Tunnell argument, where Haar integrals over $\mathrm{GL}_2(F)$ are transformed by right translations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_of_isHaarMeasure_fin_two.lean

import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Instances.Matrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Matrix

theorem Matrix.GeneralLinearGroup.isMulRightInvariant_of_isHaarMeasure_fin_two
    {F : Type*} [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by sorry
