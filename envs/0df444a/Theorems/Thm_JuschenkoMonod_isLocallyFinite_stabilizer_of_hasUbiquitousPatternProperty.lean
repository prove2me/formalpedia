-- Prove2me | Theorems.Thm_JuschenkoMonod_isLocallyFinite_stabilizer_of_hasUbiquitousPatternProperty
-- name    : JuschenkoMonod.isLocallyFinite_stabilizer_of_hasUbiquitousPatternProperty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:28:10.658449+00:00
-- url     : https://prove2.me/theorems/ca2e1f01-4cbf-49f4-b60b-a41f8a762449
-- title:
--   Lemma 4.1 — in a subgroup of W(ℤ) with the ubiquitous pattern property, the stabiliser of E △ ℕ is locally finite
-- statement:
--   Let $G$ be a subgroup of $W(\mathbf Z)$ with the ubiquitous pattern property. Then for every finite set $E \subseteq \mathbf Z$, the stabiliser in $G$ of the set $E \mathbin{\triangle} \mathbf N$ is locally finite: each of its finitely generated subgroups is finite. Here $\mathbf N = \{0, 1, 2, \dots\} \subseteq \mathbf Z$.
--
--   *Formalization note.* "$G < W(\mathbf Z)$ be a subgroup" is read as any subgroup, $W(\mathbf Z)$ itself included. $\mathbf N$ is taken to contain $0$.
-- source:
--   Juschenko, K. and Monod, N., Cantor systems, piecewise translations and simple amenable groups, Ann. of Math. (2) 178 (2013) 775–787, https://doi.org/10.4007/annals.2013.178.2.7, p. 785, Lemma 4.1

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_Chou_Classes
import Definitions.Def_JuschenkoMonod

open scoped Pointwise

namespace JuschenkoMonod

theorem isLocallyFinite_stabilizer_of_hasUbiquitousPatternProperty (G : Subgroup (Equiv.Perm ℤ))
    (hG : G ≤ IntervalExchange.wobbling ℤ) (hU : HasUbiquitousPatternProperty G) (E : Finset ℤ) :
    Chou.IsLocallyFinite (MulAction.stabilizer G (symmDiff (E : Set ℤ) natSet)) := by
  sorry

end JuschenkoMonod
