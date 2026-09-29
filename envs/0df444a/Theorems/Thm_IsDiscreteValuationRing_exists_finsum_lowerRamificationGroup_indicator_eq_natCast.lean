-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast
-- name    : IsDiscreteValuationRing.exists_finsum_lowerRamificationGroup_indicator_eq_natCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/5465c392-6055-50d4-b461-5418ee1c91ec
-- title:
--   Hasse–Arf integrality for degree-one characters
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $G$ be a finite group acting on $R$ by ring automorphisms (a multiplicative semiring action) such that the action is faithful. Assume that the maximal ideal of $R$ lies over the maximal ideal of the subring $R^{G}$ of fixed points, that the residue extension $R^{G}/\mathfrak m_{R^{G}} \to R/\mathfrak m_{R}$ is separable, and that the residue field of $R$ is perfect. Let $\psi \colon G \to \mathbb C^{\times}$ be a group homomorphism. Write $G_i :=$ [`IsLocalRing.lowerRamificationGroup R G i`](def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) for the inertia subgroup of $\mathfrak m_R^{\,i+1}$, that is, the subgroup of those $\sigma \in G$ with $\sigma x - x \in \mathfrak m_R^{\,i+1}$ for all $x \in R$. Then there is a natural number $m$ such that the rational number $$\sum_{i \ge 0} \frac{\#G_{i+1}}{\#G_0}\cdot\bigl[\,\psi|_{G_{i+1}} \neq 1\,\bigr] = m,$$ the sum being the finite sum over all $i \in \mathbb N$ (finitely many terms are nonzero) of $\#G_{i+1}/\#G_0$ times $0$ if $\psi \sigma = 1$ for every $\sigma \in G_{i+1}$ and times $1$ otherwise, equals the image of $m$ in $\mathbb Q$.
--
--   This is the Hasse–Arf theorem in the form asserting that the Swan conductor of a one-dimensional character is an integer, here for a finite group (not assumed abelian) acting faithfully on a discrete valuation ring. It is the arithmetic input to [`ArtinL.Abelian.natCeil_swanConductor_eq`](thm.html#ArtinL.Abelian.natCeil_swanConductor_eq), which identifies the Swan conductor of an abelian character with a natural number.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Classical in

theorem IsDiscreteValuationRing.exists_finsum_lowerRamificationGroup_indicator_eq_natCast
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (ψ : G →* ℂˣ) :
    ∃ m : ℕ,
      ∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G (i + 1), ψ σ = 1 then 0 else 1) = m := by sorry
