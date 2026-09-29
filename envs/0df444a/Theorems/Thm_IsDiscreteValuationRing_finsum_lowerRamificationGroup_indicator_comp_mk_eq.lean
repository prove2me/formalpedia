-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq
-- name    : IsDiscreteValuationRing.finsum_lowerRamificationGroup_indicator_comp_mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/12dd6789-4ca3-5dff-a688-4e9123b5178c
-- title:
--   Swan sum of a character is invariant under inflation
-- statement:
--   Let $R$ be a commutative domain that is a discrete valuation ring, and let $G$ be a finite group acting faithfully on $R$ by ring automorphisms, such that the maximal ideal of $R$ lies over the maximal ideal of the fixed subring $R^{G}$ and the residue field extension $R/\mathfrak{m}_R$ over $R^{G}/\mathfrak{m}_{R^{G}}$ is separable. Here, for a group $\Gamma$ acting on a local ring $S$ by ring automorphisms, [`IsLocalRing.lowerRamificationGroup S Γ i`](def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) denotes the inertia subgroup of the ideal $\mathfrak{m}_S^{\,i+1}$ in $\Gamma$, i.e. the lower-numbering ramification group $\Gamma_i$. Let $H$ be a normal subgroup of $G$, let $A$ be a commutative group and let $\chi \colon G/H \to A$ be a group homomorphism; the quotient $G/H$ acts on the fixed subring $R^{H}$. Then the two finite sums over $i, j \in \mathbb{N}$ (taken in $\mathbb{Q}$, each summand vanishing for large index) agree:
--   $$\sum_{i \ge 0} \frac{|G_{i+1}|}{|G_0|}\,\big[\chi \circ \mathrm{pr} \text{ is non-trivial on } G_{i+1}\big] \;=\; \sum_{j \ge 0} \frac{|(G/H)_{j+1}|}{|(G/H)_0|}\,\big[\chi \text{ is non-trivial on } (G/H)_{j+1}\big],$$
--   where $\mathrm{pr} \colon G \to G/H$ is the projection, the lower-numbering groups on the left are those of the action of $G$ on $R$ and on the right those of the action of $G/H$ on $R^{H}$, and each bracket is $0$ if $\chi$ (respectively its inflation) sends every element of the indicated group to $1$, and $1$ otherwise.
--
--   This is the invariance under inflation of the Swan conductor of a one-dimensional character, in the form of Serre's computation of the Artin conductor in terms of lower-numbering ramification groups (Corps locaux VI §2). It is used for the behaviour of the Swan conductor under restriction along a normal quotient ([`ArtinL.Abelian.swanConductor_comp_restrictNormalHom`](thm.html#ArtinL.Abelian.swanConductor_comp_restrictNormalHom)) and for the integrality of this sum ([`IsDiscreteValuationRing.exists_finsum_lowerRamificationGroup_indicator_eq_natCast`](thm.html#IsDiscreteValuationRing.exists_finsum_lowerRamificationGroup_indicator_eq_natCast)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped Classical in

theorem IsDiscreteValuationRing.finsum_lowerRamificationGroup_indicator_comp_mk_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] {A : Type*} [CommGroup A] (χ : G ⧸ H →* A) :
    ∑ᶠ i : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup R G (i + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup R G 0) : ℚ) *
          (if ∀ σ ∈ IsLocalRing.lowerRamificationGroup R G (i + 1), χ (QuotientGroup.mk σ) = 1 then 0 else 1) =
      ∑ᶠ j : ℕ,
        (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) : ℚ) /
            (Nat.card (IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) 0) : ℚ) *
          (if ∀ τ ∈ IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1), χ τ = 1
            then 0 else 1) := by sorry
