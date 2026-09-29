-- Prove2me | Theorems.Thm_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card
-- name    : M4aLocalCFT.fieldUnitsDecomp_herbrandQuotient_eq_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/7aeeff9e-283a-5cc0-8c45-808fdb6bc0f1
-- title:
--   Herbrand quotient |G| for L^× under a cyclic decomposition group
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a valuation subring of $L$ which is a discrete valuation ring, adically complete for its maximal ideal, with finite residue field, and whose decomposition subgroup $G =$ `A.decompositionSubgroup K` (the subgroup of $K$-algebra automorphisms of $L$ preserving $A$) is finite and cyclic. Let $g \in G$ be such that every element of $G$ lies in the subgroup of integer powers of $g$, i.e. $g$ generates $G$. Two endomorphisms of the abelian group $L^\times$ are involved: `fieldUnitsNorm` $= \prod_{s \in G} s$, the product over $G$ of the maps induced on units by the automorphisms $s$, and `fieldUnitsDerive` for $g$, namely $u \mapsto g(u)/u$. The assertion is the conjunction of two statements: first, the cardinality of $\ker(u \mapsto g(u)/u)$ modulo the image of the norm map intersected with that kernel equals $\#G$ times the cardinality of $\ker(\text{norm})$ modulo the image of $u \mapsto g(u)/u$ intersected with that kernel; second, this latter cardinality is nonzero, i.e. the quotient is finite.
--
--   In classical terms this is the computation of the Herbrand quotient $h(G, L^\times) = \#\hat H^0(G,L^\times)/\#\hat H^{-1}(G,L^\times) = \#G$ for a cyclic decomposition group acting on the multiplicative group of a complete discretely valued field with finite residue field; the order $\#G$ appears as such, with no identification with $[L:K]$. It feeds the computation of $\#\hat H^0(G, L^\times)$ and, through that, the divisibility of the index of the norm group used for quadratic extensions of number fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aLocalCFT_fieldUnitsDecomp_herbrandQuotient_eq_card.lean

import Definitions.Def_M4aLocalCFT_VocabDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace M4aLocalCFT

section LocalUnitCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L) [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]

variable (K) in

theorem fieldUnitsDecomp_herbrandQuotient_eq_card
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((fieldUnitsDerive A g).ker ⧸
      ((fieldUnitsNorm (K := K) A).range.subgroupOf (fieldUnitsDerive A g).ker)) =
    Nat.card (A.decompositionSubgroup K) *
    Nat.card ((fieldUnitsNorm (K := K) A).ker ⧸
      ((fieldUnitsDerive A g).range.subgroupOf (fieldUnitsNorm (K := K) A).ker)) ∧
    Nat.card ((fieldUnitsNorm (K := K) A).ker ⧸
      ((fieldUnitsDerive A g).range.subgroupOf (fieldUnitsNorm (K := K) A).ker)) ≠ 0 := by sorry
