-- Prove2me | Theorems.Thm_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot
-- name    : M4aLocalCFT.unitsDecomp_cohTrivial_of_inertia_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/85230d51-4be1-53ce-aeae-1bc4c1fb69f5
-- title:
--   Unramified local units: both Tate vanishings for cyclic G
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a valuation subring of $L$ which is a discrete valuation ring, adically complete for its maximal ideal and with finite residue field. Write $G :=$ `A.decompositionSubgroup K` for the subgroup of $K$-algebra automorphisms of $L$ stabilising $A$, and assume $G$ is finite and cyclic. For $s \in G$ let `unitsAct A s` be the induced automorphism of the unit group $A^\times$, let `unitsNorm A` be the product $\prod_{s \in G}$ `unitsAct A s` of these automorphisms (a monoid endomorphism of $A^\times$, i.e. the norm $u \mapsto \prod_{s} s(u)$), and for $g \in G$ let `unitsDerive A g` be the quotient of `unitsAct A g` by the identity, i.e. $u \mapsto g(u)\,u^{-1}$. The theorem assumes given an element $g \in G$ such that every element of $G$ lies in `Subgroup.zpowers g`, and that the inertia subgroup `A.inertiaSubgroup K` is trivial. Its conclusion is the conjunction of two inclusions: the kernel of `unitsDerive A g`, that is the $G$-invariant units, is contained in the image of `unitsNorm A`; and the kernel of `unitsNorm A`, that is the units of norm $1$, is contained in the image of `unitsDerive A g`.
--
--   These two inclusions are exactly the vanishing of the Tate groups $\hat H^{0}(G, A^\times)$ and $\hat H^{-1}(G, A^\times)$ for the cyclic group $G$, i.e. cohomological triviality of the units of an unramified complete discrete valuation ring with finite residue field; nothing is asserted about the ramified case, about $|G| = [L:K]$, or about identifying $G$ with a Galois group. It is used in the local and idelic norm computations of the class field theory input, being cited by [`IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot`](thm.html#IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot), [`M4aHerbrand.unitIdele_mem_idelicNorm_range`](thm.html#M4aHerbrand.unitIdele_mem_idelicNorm_range) and [`NumberField.PlaceDecomp.subsingleton_tate_integerUnits_of_unramified`](thm.html#NumberField.PlaceDecomp.subsingleton_tate_integerUnits_of_unramified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot.lean

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

theorem unitsDecomp_cohTrivial_of_inertia_eq_bot
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hur : A.inertiaSubgroup K = ⊥) :
    (unitsDerive A g).ker ≤ (unitsNorm (K := K) A).range ∧
    (unitsNorm (K := K) A).ker ≤ (unitsDerive A g).range := by sorry
