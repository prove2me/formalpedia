-- Prove2me | Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
-- name    : NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/aa752c39-c5ca-5207-bb06-fb764ab41b62
-- title:
--   Finitely many principal adeles in a compact set
-- statement:
--   Let $F$ be a field carrying the structure of a number field, with ring of integers $\mathcal{O}_F$, and let $\mathbb{A}_F = \mathrm{AdeleRing}(\mathcal{O}_F, F)$ be its adele ring (the product of the infinite adele ring of $F$ and the finite adele ring of $\mathcal{O}_F$ in $F$). Let $C$ be any subset of $\mathbb{A}_F$ which is compact for the adelic topology. Then the set of those $\xi \in F$ whose image under the canonical algebra map $F \to \mathbb{A}_F$ (the diagonal embedding of $F$ as principal adeles) lies in $C$ is a finite subset of $F$. No further hypotheses are imposed on $C$: it need not be a subgroup, a neighbourhood of a point, or measurable. This is the quantitative form of the discreteness of $F$ in $\mathbb{A}_F$; it is stated as the finiteness of a set of elements of $F$, not as a `DiscreteTopology` instance on the image, and it asserts nothing about cocompactness of $F$ in $\mathbb{A}_F$ or about measures. For $C = \varnothing$ the set is empty, while compactness cannot be dropped, since $C = \mathbb{A}_F$ yields all of the infinite set $F$.
--
--   This is the classical statement that a number field is discrete in its adele ring, in the sharper form that compact (hence bounded) adelic regions contain only finitely many principal adeles. It is used throughout the analytic side of the development, for instance to show that sums over $F$ attached to compactly supported functions on adelic groups have finitely many nonzero terms in the trace and integral computations for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact.lean

import Mathlib.NumberTheory.NumberField.AdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact
    (F : Type) [Field F] [NumberField F]
    {C : Set (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    {ξ : F | algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C}.Finite := by sorry
