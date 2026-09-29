-- Prove2me | Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
-- name    : MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/8d11ff17-1751-5af7-932b-bc99d25b338e
-- title:
--   Unimodular Haar measure is inversion invariant
-- statement:
--   Let $G$ be a group carrying a topology for which it is a topological group and which is locally compact and second countable, equipped with a measurable space structure that is the Borel $\sigma$-algebra of the topology. Let $\mu$ be a measure on $G$ which is a Haar measure in the sense of Mathlib's `Measure.IsHaarMeasure`, that is, left invariant under multiplication, regular, finite on compact sets and positive on nonempty open sets, and suppose in addition that $\mu$ is invariant under right multiplication. The conclusion is that $\mu$ satisfies `Measure.IsInvInvariant`: the push-forward of $\mu$ along the inversion map $g \mapsto g^{-1}$ is again $\mu$, equivalently $\mu(A^{-1}) = \mu(A)$ for every Borel set $A \subseteq G$. Thus on a second countable locally compact group a bi-invariant Haar measure is automatically invariant under inversion.
--
--   This is the classical statement that a unimodular group's Haar measure is inversion invariant; Mathlib supplies it for commutative groups, and this is the general two-sided invariant case. It is used in the construction and manipulation of convolution operators and idempotent kernels on automorphic forms, where the groups in play are bi-invariant (for instance compact modulo the centre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by sorry
