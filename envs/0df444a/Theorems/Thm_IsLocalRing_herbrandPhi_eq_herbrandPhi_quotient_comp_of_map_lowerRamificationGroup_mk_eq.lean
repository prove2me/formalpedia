-- Prove2me | Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
-- name    : IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/152f42ec-2a90-5909-91a9-f2728a1c64f7
-- title:
--   Transitivity of the Herbrand function: φ_G = φ_{G/H}∘φ_H
-- statement:
--   Let $R$ be a commutative local ring carrying a ring action of a finite group $G$, let $H$ be a normal subgroup of $G$, and let $S$ be a second commutative local ring carrying a ring action of the quotient group $G/H$. For a group $\Gamma$ acting on a local ring $B$, the $n$-th lower ramification group is the inertia subgroup of $\Gamma$ on the ideal $\mathfrak m_B^{\,n+1}$, i.e. the subgroup of elements acting trivially on $B/\mathfrak m_B^{\,n+1}$; writing $g_n$ for its cardinality (as a natural number), the associated Herbrand function is $\varphi_\Gamma(u) = u$ for $u \le 0$ and $\varphi_\Gamma(u) = \bigl(\sum_{i=1}^{\lfloor u\rfloor} g_i + (u - \lfloor u\rfloor) g_{\lfloor u\rfloor + 1}\bigr)/g_0$ for $u > 0$, where $\lfloor\cdot\rfloor$ is the floor taken in $\mathbb N$. The hypothesis is Herbrand's theorem in the lower numbering, sampled at integers: for every natural number $n$, the image of the $n$-th lower ramification group of $G$ acting on $R$ under the projection $G \to G/H$ equals the lower ramification group of $G/H$ acting on $S$ with index $\lceil \varphi_H(n)\rceil$, the ceiling in $\mathbb N$ of the Herbrand function of $H$ acting on $R$ by restriction. The conclusion is that for every rational $u \ge 0$ one has $\varphi_G(u) = \varphi_{G/H}\bigl(\varphi_H(u)\bigr)$, the outer function computed for the action of $G/H$ on $S$.
--
--   This is the transitivity (composition) formula for Herbrand's function, Proposition 15 of Chapter IV §3 of Serre's *Corps locaux*, stated for group actions on local rings with Herbrand's theorem in the lower numbering taken as a hypothesis. It feeds the compatibility of the upper numbering with quotients, the corresponding statement for valuation subrings attached to places of number fields, and an estimate for upper ramification groups over a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup S (G ⧸ H) ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊)
    {u : ℚ} (hu : 0 ≤ u) :
    IsLocalRing.herbrandPhi R G u =
      IsLocalRing.herbrandPhi S (G ⧸ H) (IsLocalRing.herbrandPhi R H u) := by sorry
