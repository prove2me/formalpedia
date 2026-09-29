-- Prove2me | Theorems.Thm_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex
-- name    : M4aLocalCFT.unitsDecomp_exists_cohTrivial_finiteIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e8559e9b-0e04-5733-b2de-7d9fd23710a1
-- title:
--   Finite-index cohomologically trivial subgroup of local units
-- statement:
--   Let $K$ and $L$ be fields with $L$ an algebra over $K$, and let $A$ be a valuation subring of $L$ which is a discrete valuation ring, complete for the adic topology of its maximal ideal, with finite residue field. Assume the decomposition subgroup $G = A.\mathrm{decompositionSubgroup}\,K$ (the subgroup of $K$-automorphisms of $L$ preserving $A$) is finite, and let $g \in G$ be such that every element of $G$ lies in the subgroup of integer powers of $g$, i.e. $G$ is cyclic with generator $g$. For $s \in G$ write $s \cdot v$ for the action [`M4aLocalCFT.unitsAct A s`](def/M4aLocalCFT_VocabDefs.html#L21) of $s$ on $A^{\times}$ induced by the ring automorphism of $A$ attached to $s$, let [`M4aLocalCFT.unitsNorm`](def/M4aLocalCFT_VocabDefs.html#L24) be the product homomorphism $N(v) = \prod_{s \in G} s \cdot v$ on $A^{\times}$, and let [`M4aLocalCFT.unitsDerive A g`](def/M4aLocalCFT_VocabDefs.html#L28) be the homomorphism $D(v) = (g \cdot v)\, v^{-1}$. The assertion is that there exists a subgroup $V \le A^{\times}$ of finite index such that $s \cdot v \in V$ for all $s \in G$ and $v \in V$; every $v \in V$ with $D(v) = 1$ equals $N(w)$ for some $w \in V$; and every $v \in V$ with $N(v) = 1$ equals $D(w)$ for some $w \in V$.
--
--   This is the approximation lemma of local class field theory which exhibits, inside the unit group of a complete discrete valuation ring, a finite-index $G$-stable subgroup whose Tate cohomology in degrees $0$ and $-1$ vanishes in the witnessed form above. It is used to compute the Herbrand quotient $h(G, A^{\times}) = 1$ in [`M4aLocalCFT.unitsDecomp_herbrandQuotient_eq_one`](thm.html#M4aLocalCFT.unitsDecomp_herbrandQuotient_eq_one), and its proof cites the integral normal basis statement [`M4aLocalCFT.decompositionSubgroup_exists_integralNormalBasis`](thm.html#M4aLocalCFT.decompositionSubgroup_exists_integralNormalBasis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.lean

import Definitions.Def_M4aLocalCFT_VocabDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aLocalCFT.unitsDecomp_exists_cohTrivial_finiteIndex
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ V : Subgroup Aˣ, V.FiniteIndex ∧
      (∀ s : A.decompositionSubgroup K, ∀ v ∈ V, M4aLocalCFT.unitsAct A s v ∈ V) ∧
      (∀ v ∈ V, M4aLocalCFT.unitsDerive A g v = 1 →
        ∃ w ∈ V, M4aLocalCFT.unitsNorm (K := K) A w = v) ∧
      (∀ v ∈ V, M4aLocalCFT.unitsNorm (K := K) A v = 1 →
        ∃ w ∈ V, M4aLocalCFT.unitsDerive A g w = v) := by sorry
