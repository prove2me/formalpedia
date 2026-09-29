-- Prove2me | Theorems.Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
-- name    : IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/17f30513-5025-521c-aecf-5cb33da3b084
-- title:
--   Herbrand's theorem in the upper numbering for quotients
-- statement:
--   Let $R$ and $S$ be commutative local rings, let $G$ be a finite group acting on $R$ by ring automorphisms, let $H$ be a normal subgroup of $G$ (acting on $R$ by restriction), and let the quotient group $G/H$ act on $S$ by ring automorphisms. For a group $\Gamma$ acting this way on a local ring $B$, write $\Gamma_i$ for `lowerRamificationGroup`, the inertia subgroup of $\mathfrak m_B^{\,i+1}$, write $c_\Gamma(i)=\operatorname{Nat.card}\Gamma_i$, and let $\varphi_\Gamma(u)=u$ for $u\le 0$ and $\varphi_\Gamma(u)=\bigl(\sum_{i=1}^{\lfloor u\rfloor}c_\Gamma(i)+(u-\lfloor u\rfloor)c_\Gamma(\lfloor u\rfloor+1)\bigr)/c_\Gamma(0)$ otherwise; the upper-numbering group $\Gamma^v$ is $\Gamma_{i}$ for $i=$ `upperRamificationIndex` $\Gamma\,v$, the natural-number index attached to the rational $v$. The hypothesis is the lower-numbering form of Herbrand's theorem, sampled at integers: for every $n\in\mathbb N$ the image of $G_n$ under the quotient homomorphism $G\to G/H$ equals $(G/H)_{\lceil\varphi_H(n)\rceil}$, the ceiling being the natural-number ceiling of $\varphi_H$ computed for the restricted action of $H$ on $R$. The conclusion is the predicate `UpperRamificationQuotientCompat` for $R$, $G$, $S$, $H$: for every rational $v\ge 0$, the image of $G^v$ in $G/H$ equals $(G/H)^v$.
--
--   This is Herbrand's theorem in the upper numbering (Serre, *Corps locaux* IV §3, Prop. 14), here stated abstractly for finite group actions on local rings: the upper numbering is compatible with passage to a quotient group, granted the lower-numbering statement at integral indices. It is used in the discrete-valuation setting, both for the Hasse–Arf chain of lower ramification groups under cyclicity of quotients and for the upper-numbering quotient compatibility in the case of separable residue field extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (IsLocalRing.lowerRamificationGroup R G n).map (QuotientGroup.mk' H) =
        IsLocalRing.lowerRamificationGroup S (G ⧸ H) ⌈IsLocalRing.herbrandPhi R H (n : ℚ)⌉₊) :
    IsLocalRing.UpperRamificationQuotientCompat R G S H := by sorry
