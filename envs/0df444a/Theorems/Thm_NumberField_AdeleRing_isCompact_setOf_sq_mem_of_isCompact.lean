-- Prove2me | Theorems.Thm_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact
-- name    : NumberField.AdeleRing.isCompact_setOf_sq_mem_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9a859a46-1683-5917-90ef-c387a6810c67
-- title:
--   Squaring is proper on the idele group
-- statement:
--   Let $K$ be a number field, and let $\mathbb{A}_K^\times$ denote the unit group $(\mathtt{AdeleRing }(\mathcal{O}_K)\ K)^\times$ of the adele ring of $K$ over its ring of integers, carried with its usual topology as the unit group of a topological ring. Let $C \subseteq \mathbb{A}_K^\times$ be a subset of the idele group which is compact. The conclusion is that the set $\{u \in \mathbb{A}_K^\times : u^2 \in C\}$ of ideles whose square lies in $C$ is again compact. Equivalently, the squaring endomorphism $u \mapsto u^2$ of the idele group is a proper map: preimages of compact sets are compact. Note that the assertion is about compactness of the full preimage $\{u : u^2 \in C\}$, not merely of a single fibre, and that no hypothesis beyond compactness (such as closedness of $C$ in the adeles, or containment in a norm-one subgroup) is imposed.
--
--   This is the properness of the squaring map on the idele group of a number field, the compactness statement underlying the fact that an idele has only a compact set of square roots lying over a compact set of values. It is used to bound the central parameter in orbital integrals of central translates, through the determinant, and in the estimate for the Haar quotient of the kernel of the idelic norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_isCompact_setOf_sq_mem_of_isCompact.lean

import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.isCompact_setOf_sq_mem_of_isCompact
    (K : Type) [Field K] [NumberField K]
    (C : Set (AdeleRing (𝓞 K) K)ˣ) (hC : IsCompact C) :
    IsCompact {u : (AdeleRing (𝓞 K) K)ˣ | u ^ 2 ∈ C} := by sorry
