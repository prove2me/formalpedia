-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
-- name    : IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/2f2b7068-c52e-5456-ad0a-75d3c4abc311
-- title:
--   Herbrand's theorem for lower ramification groups
-- statement:
--   Let $R$ be a discrete valuation ring that is a domain, with additive valuation $v_R =$ `IsDiscreteValuationRing.addVal R` taking values in $\mathbb N_\infty$, and let a group $G$ act faithfully on $R$ by ring automorphisms. Let $H$ be a finite normal subgroup of $G$ such that the subring $R^H$ of $H$-fixed points is again a discrete valuation ring. For a group $\Gamma$ acting on a local ring $B$ write $\Gamma_i$ for the inertia subgroup of $\mathfrak m_B^{\,i+1}$, i.e. the elements acting trivially on $B/\mathfrak m_B^{\,i+1}$, and put $i_\Gamma(\sigma) = \inf_{x \in B} v_B(\sigma x - x)$. Assume: (1) for every $\tau \in G$, with $\bar\tau$ its class in $G/H$, one has $\inf_{z \in R^H} v_R(\bar\tau z - z) = \sum_{h \in H} i_G(\tau h)$, the infimum and the sum taken in $\mathbb N_\infty$; (2) for every $z \in R^H$, $v_R(z) = |H_0| \cdot v_{R^H}(z)$, where $|H_0|$ is the cardinality of $H_0$. Then for every $n \in \mathbb N$ the image of $G_n$ under $G \to G/H$ equals $(G/H)_m$, the ramification group of $G/H$ acting on $R^H$ at $m = \lceil \varphi_H(n) \rceil$ (ceiling taken in $\mathbb N$), where $\varphi_H$ is the Herbrand function of $H$ acting on $R$, given for $u > 0$ by $\varphi_H(u) = \bigl(\sum_{i=1}^{\lfloor u \rfloor} |H_i| + (u - \lfloor u \rfloor)\,|H_{\lfloor u \rfloor + 1}|\bigr)/|H_0|$ and by $\varphi_H(u) = u$ for $u \le 0$.
--
--   This is Herbrand's theorem in the lower numbering (Serre, Corps locaux, IV §3, Lemma 5 and Proposition 14), in an abstract form in which the two arithmetic inputs — the formula for the ramification depth of a class in $G/H$ as a sum over $H$, and the comparison of the valuations of $R$ and $R^H$ through the ramification index $|H_0|$ — are taken as hypotheses. It is used by [`IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top`](thm.html#IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top), where these hypotheses are supplied in the monogenic situation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {H : Subgroup G} [H.Normal] [Fintype H] [IsDiscreteValuationRing (FixedPoints.subring R H)]
    (hH : ∀ τ : G,
      (⨅ z : FixedPoints.subring R H,
          IsDiscreteValuationRing.addVal R
            (((QuotientGroup.mk τ : G ⧸ H) • z - z : FixedPoints.subring R H) : R)) =
        ∑ h : H, IsDiscreteValuationRing.ramificationDepth R G (τ * (h : G)))
    (he : ∀ z : FixedPoints.subring R H,
      IsDiscreteValuationRing.addVal R (z : R) =
        (IsLocalRing.lowerRamificationCard R H 0 : ℕ∞) *
          IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z)
    (n : ℕ) :
    (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
      IsLocalRing.lowerRamificationGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊ := by sorry
