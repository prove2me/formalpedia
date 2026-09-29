-- Prove2me | Theorems.Thm_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one
-- name    : M4aLocalCFT.unitsDecomp_herbrandQuotient_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/ad42d7dc-17ae-5406-9d1d-016e5d077f5b
-- title:
--   Herbrand quotient of the units of a complete DVR equals one
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A \subseteq L$ be a valuation subring which is a discrete valuation ring, adically complete for its maximal ideal and with finite residue field; assume the decomposition subgroup $G = A.\mathrm{decompositionSubgroup}\,K$ (the subgroup of $K$-automorphisms of $L$ preserving $A$) is finite and cyclic. Let $g \in G$ be such that every element of $G$ lies in the subgroup of integral powers of $g$. Two endomorphisms of the abelian group $A^\times$ are involved: `unitsNorm`, the product $\prod_{s \in G} \mathrm{unitsAct}\,A\,s$ of the automorphisms of $A^\times$ induced by the elements of $G$, written $N$; and `unitsDerive` at $g$, the quotient homomorphism $u \mapsto g(u)/u$, written $D$. The conclusion is the conjunction of two assertions: the cardinality of $\ker D / \mathrm{im}\,N$ (the image of $N$ viewed as a subgroup of $\ker D$) equals the cardinality of $\ker N / \mathrm{im}\,D$, and the former cardinality is nonzero, i.e. that quotient is finite.
--
--   This is the statement that the Herbrand quotient of the unit group $A^\times$ under a finite cyclic decomposition group is trivial: the Tate cohomology groups $\hat H^0(G, A^\times)$ and $\hat H^{-1}(G, A^\times)$ have the same finite order. It feeds the computation of the Herbrand quotient of $L^\times$ in [`M4aLocalCFT.fieldUnitsDecomp_herbrandQuotient_eq_card`](thm.html#M4aLocalCFT.fieldUnitsDecomp_herbrandQuotient_eq_card), within the local class field theory input. Neither the separate vanishing of the two groups (the unramified phenomenon) nor the equality $|G| = [L:K]$ is asserted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aLocalCFT_unitsDecomp_herbrandQuotient_eq_one.lean

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

theorem unitsDecomp_herbrandQuotient_eq_one
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card ((unitsDerive A g).ker ⧸
      ((unitsNorm (K := K) A).range.subgroupOf (unitsDerive A g).ker)) =
    Nat.card ((unitsNorm (K := K) A).ker ⧸
      ((unitsDerive A g).range.subgroupOf (unitsNorm (K := K) A).ker)) ∧
    Nat.card ((unitsDerive A g).ker ⧸
      ((unitsNorm (K := K) A).range.subgroupOf (unitsDerive A g).ker)) ≠ 0 := by sorry
