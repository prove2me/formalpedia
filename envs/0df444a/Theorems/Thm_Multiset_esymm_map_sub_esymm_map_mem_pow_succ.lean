-- Prove2me | Theorems.Thm_Multiset_esymm_map_sub_esymm_map_mem_pow_succ
-- name    : Multiset.esymm_map_sub_esymm_map_mem_pow_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/ba3027d0-f017-5f97-852f-3b1232f7adc7
-- title:
--   Elementary symmetric functions modulo powers of an ideal
-- statement:
--   Let $A$ be a commutative ring, $I \subseteq A$ an ideal, $\iota$ a type, $s$ a finite subset of $\iota$, and $y, z : \iota \to A$ two families of ring elements. Assume that $z_i \in I$ for every $i \in s$, and that $y_i - z_i \in I^2$ for every $i \in s$. Then for every natural number $k$, the difference of the $k$-th elementary symmetric functions of the two families, formed as the `Multiset.esymm` of degree $k$ of the multisets $s.val.map\ y$ and $s.val.map\ z$ obtained by pushing the underlying multiset of $s$ forward along $y$ and along $z$ respectively — that is, $\sum_{t \subseteq s,\ |t| = k} \prod_{i \in t} y_i$ minus $\sum_{t \subseteq s,\ |t| = k} \prod_{i \in t} z_i$ — lies in $I^{k+1}$. No hypothesis is imposed on $y_i$ or $z_i$ for indices outside $s$, and no restriction is placed on $k$ relative to the cardinality of $s$; the degenerate cases $k = 0$ and $k > |s|$ are included, the latter because both symmetric functions then vanish.
--
--   This is the statement that a congruence $y \equiv z \pmod{I^2}$ between families of elements of $I$ propagates to the elementary symmetric functions with a gain of one power of $I$ per degree. It is used, via Vieta's formulae, in the analysis of the coefficients of the characteristic-type product over the points of a Drinfeld basis, in [`FormalGroup.IsDrinfeldBasisAdic.exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_mem_pow_isUnit_homogeneous_of_coeff_nthSeries_of_ringEquiv_drinfeldChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Multiset_esymm_map_sub_esymm_map_mem_pow_succ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Multiset.esymm_map_sub_esymm_map_mem_pow_succ
    (A : Type) [CommRing A] (I : Ideal A) (ι : Type) (s : Finset ι) (y z : ι → A)
    (hz : ∀ i ∈ s, z i ∈ I) (hyz : ∀ i ∈ s, y i - z i ∈ I ^ 2) (k : ℕ) :
    (s.val.map y).esymm k - (s.val.map z).esymm k ∈ I ^ (k + 1) := by sorry
