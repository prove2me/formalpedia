-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
-- name    : IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/b2bafc30-7de1-5349-97bf-4779ec7d0332
-- title:
--   Herbrand's theorem in the lower numbering
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain) and let $G$ be a finite group acting faithfully on $R$ by ring automorphisms, and write $R^G =$ `FixedPoints.subring R G` for the subring of invariants. Assume the maximal ideal of $R$ lies over that of $R^G$ (i.e. $\mathfrak m_{R^G}$ is the contraction of $\mathfrak m_R$), and that $R/\mathfrak m_R$ is separable over $R^G/\mathfrak m_{R^G}$. Let $H$ be a normal subgroup of $G$ and $n$ a natural number. For a group $\Gamma$ acting on a local ring $B$, the $i$-th ramification group in the lower numbering is the inertia subgroup of $\mathfrak m_B^{\,i+1}$, namely those $\sigma \in \Gamma$ acting trivially on $B/\mathfrak m_B^{\,i+1}$, and the Herbrand function is $\varphi_\Gamma(u) = u$ for $u \le 0$ and otherwise $\bigl(\sum_{i=1}^{\lfloor u\rfloor}\#\Gamma_i + (u-\lfloor u\rfloor)\,\#\Gamma_{\lfloor u\rfloor+1}\bigr)/\#\Gamma_0$. The conclusion is that the image of $G_n$ under the projection $G \to G/H$ equals the $\lceil \varphi_H(n)\rceil$-th ramification group of $G/H$ acting on $R^H$, where $\varphi_H$ is computed for $H$ acting on $R$ and the ceiling is the natural-number ceiling of the rational $\varphi_H(n) = \bigl(\sum_{i=1}^{n}\#H_i\bigr)/\#H_0$.
--
--   This is Herbrand's theorem, Proposition 14 of Chapter IV, §3 of Serre's *Corps locaux*, in the lower numbering and for an abstract faithful action of a finite group on a discrete valuation ring with separable residue extension, no monogenicity or ramification-index hypothesis being imposed. It feeds the passage to the upper numbering and the associated counting and summation identities for ramification groups used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    {H : Subgroup G} [H.Normal] (n : ℕ) :
    (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊ := by sorry
