-- Prove2me | Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField
-- name    : IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/41a0ecc1-93b0-584f-97d8-1dae58f43cda
-- title:
--   Dominating DVR with finite residue field in a finite extension
-- statement:
--   Let $A$ be a Noetherian local domain whose Krull dimension `ringKrullDim A` equals $1$ and whose residue field is finite, let $K$ be a field that is a fraction field of $A$, and let $L$ be a field which is an $A$-algebra and a $K$-algebra compatibly (a scalar tower $A \to K \to L$) and which is finite as a $K$-module. The assertion is that there exists a valuation subring $V$ of $L$ such that: $V$ is a discrete valuation ring; the image $\operatorname{alg}_{A,L}(a)$ of every $a \in A$ lies in $V$, so that $V$ contains the image of $A$; for every $a \in A$ one has $a \in \mathfrak m_A$ if and only if $\operatorname{alg}_{A,L}(a)$ belongs to `V.nonunits`, i.e. lies in $V$ and is not a unit of $V$ — in other words $V$ dominates the image of $A$, $\mathfrak m_A$ being the preimage of $\mathfrak m_V$; and the residue field of $V$ is finite.
--
--   This is the existence of a dominating discrete valuation ring in a finite extension of the fraction field, in the form that also preserves finiteness of the residue field, the finiteness statement resting on the Krull–Akizuki theorem. It is used by [`AlgebraicGeometry.exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes`](thm.html#AlgebraicGeometry.exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes), which produces valuative commutative squares over discrete valuation rings with finite residue field realising a specialisation of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open IsLocalRing

theorem IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (hA : ringKrullDim A = 1)
    [Finite (ResidueField A)]
    {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type w} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing ↥V ∧
      (∀ a : A, algebraMap A L a ∈ V) ∧
      (∀ a : A, a ∈ maximalIdeal A ↔ algebraMap A L a ∈ V.nonunits) ∧
      Finite (ResidueField ↥V) := by sorry
