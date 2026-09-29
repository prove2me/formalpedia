-- Prove2me | Theorems.Thm_M4aHerbrand_Bridge_genuineBeta_comp_of_tower
-- name    : M4aHerbrand.Bridge.genuineBeta_comp_of_tower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/ea6bf1f1-a96e-5a5a-b46b-63a06582e44c
-- title:
--   Transitivity of adèle base change in a tower
-- statement:
--   Let $K$, $K'$ and $K''$ be number fields (types carrying a field structure together with a `NumberField` instance), equipped with algebra structures $K \to K'$, $K' \to K''$ and $K \to K''$ that are compatible, i.e. form a scalar tower, so that $K''$ is an extension of $K'$ which is an extension of $K$ and the given map $K \to K''$ is the composite. For an extension $L/K$ of number fields, `genuineβ K L` denotes the base-change ring homomorphism from the adèle ring of $K$, presented as the product of the infinite adèle ring and the finite adèle ring of the ring of integers, to that of $L$; its archimedean component is the conorm attached to `genuineInfinitePlaceData`, acting at an infinite place $w$ of $L$ by the canonical map from the completion at $w \circ (\text{the structure map})$ to the completion at $w$, and its non-archimedean component is `finiteConorm`, acting at a height-one prime $w$ of $\mathcal{O}_L$ by the semialgebra map of adic completions over the prime of $\mathcal{O}_K$ lying under $w$. The theorem asserts the equality of ring homomorphisms: `genuineβ K K'` followed by `genuineβ K' K''` equals `genuineβ K K''`, from the adèles of $K$ to the adèles of $K''$.
--
--   This is the transitivity (functoriality in towers) of the adèle base-change map, the adelic counterpart of the compatibility of completions and of the maps $K_v \to K''_{w}$ in a tower $K \subseteq K' \subseteq K''$. It is used downstream for the corresponding statements about idèles and idèle class groups, in particular in the Galois-descent results on idèle class groups and in the statements comparing invariants along a scalar tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_Bridge_genuineBeta_comp_of_tower.lean

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField M4aHerbrand.Bridge

theorem M4aHerbrand.Bridge.genuineBeta_comp_of_tower
    (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field K''] [NumberField K'']
    [Algebra K K'] [Algebra K' K''] [Algebra K K''] [IsScalarTower K K' K''] :
    (genuineβ K' K'').comp (genuineβ K K') = genuineβ K K'' := by sorry
