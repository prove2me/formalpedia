-- Prove2me | Theorems.Thm_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis
-- name    : M4aLocalCFT.decompositionSubgroup_exists_integralNormalBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/87602f98-c614-5163-b476-cb272ffdc996
-- title:
--   Integral normal basis with invariant denominator for a valuation ring
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $A$ be a valuation subring of $L$. Write $G = A.\mathrm{decompositionSubgroup}\ K$ for the decomposition subgroup of $A$ inside the $K$-algebra automorphisms of $L$, i.e. the stabiliser of $A$, and assume $G$ is finite (the finiteness is used to index a finite sum). Let $F = L^{G}$ denote the subfield of elements of $L$ fixed by $G$. The assertion is that there exists $\alpha \in A$ such that the family of conjugates $(s \cdot \alpha)_{s \in G}$ is linearly independent over $F$, together with an element $d \in A$ with $d \neq 0$ and $s \cdot d = d$ for every $s \in G$, having the property that for every $a \in A$ there is a family of coefficients $c : G \to L$ with $c_s \in A$ for all $s$, with $t \cdot c_s = c_s$ for all $s, t \in G$ (so each $c_s$ lies in $A \cap F$), and with $d\,a = \sum_{s \in G} c_s \, (s \cdot \alpha)$. Only linear independence of the conjugates over $F$ is asserted, not that they span $L$.
--
--   This is the lattice step in the computation of the cohomology of the units of a local field: an integral normal basis element $\alpha$ for $L$ over the fixed field of the decomposition group, whose $A \cap F$-span contains $d\,A$ for one fixed invariant denominator $d$. It is used by [`M4aLocalCFT.unitsDecomp_exists_cohTrivial_finiteIndex`](thm.html#M4aLocalCFT.unitsDecomp_exists_cohTrivial_finiteIndex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis.lean

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Fixed
import Mathlib.Algebra.BigOperators.Pi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem M4aLocalCFT.decompositionSubgroup_exists_integralNormalBasis
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Finite (A.decompositionSubgroup K)] :
    letI := Fintype.ofFinite (A.decompositionSubgroup K)
    ∃ α : L, α ∈ A ∧
      LinearIndependent (FixedPoints.subfield (A.decompositionSubgroup K) L)
        (fun s : A.decompositionSubgroup K => s • α) ∧
      ∃ d : L, d ∈ A ∧ d ≠ 0 ∧ (∀ s : A.decompositionSubgroup K, s • d = d) ∧
        ∀ a : L, a ∈ A → ∃ c : A.decompositionSubgroup K → L,
          (∀ s, c s ∈ A) ∧ (∀ s t : A.decompositionSubgroup K, t • c s = c s) ∧
          d * a = ∑ s, c s * s • α := by sorry
