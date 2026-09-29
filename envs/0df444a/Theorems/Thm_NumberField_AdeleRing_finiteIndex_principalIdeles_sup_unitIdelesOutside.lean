-- Prove2me | Theorems.Thm_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside
-- name    : NumberField.AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/d284e1f3-279a-52ca-b676-ebed9ee94e3f
-- title:
--   Finite index of principal times S-unit idèles
-- statement:
--   Let $E$ and $K$ be number fields, with $K$ given as an $E$-algebra, and let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_E$. Put $T=\{w \mid w\text{ lies under a prime of }S\}$, i.e. the set of height-one primes $w$ of $\mathcal{O}_K$ whose contraction `w.under (𝓞 E)` to $\mathcal{O}_E$ belongs to $S$. Inside the unit group of the adèle ring $\mathbb{A}_K$ of $K$ consider two subgroups: [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16), the image of $K^\times$ under the map of unit groups induced by the structure morphism $K \to \mathbb{A}_K$; and [`NumberField.AdeleRing.unitIdelesOutside`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) for the set $T$, consisting of those adèlic units $\delta$ whose finite part satisfies, at every height-one prime $v \notin T$, that both $\delta_v$ and $(\delta^{-1})_v$ lie in the valuation ring $\mathcal{O}_{K_v}$ of the $v$-adic completion (this subgroup being defined by pulling back the corresponding subgroup of the finite-adèle units along the projection to the finite adèles). The assertion is that the join of these two subgroups has finite index in $\mathbb{A}_K^\times$.
--
--   This is the idèlic form of the finiteness of the $S$-class group of $K$: the quotient of $\mathbb{A}_K^\times$ by principal idèles together with the idèles that are units outside the primes above $S$ is a quotient of the ideal class group of $\mathcal{O}_K$, hence finite. The statement supplies the finite-index hypothesis needed in the cohomological arguments on idèle class groups, and is used in the treatment of local invariants, of level arithmetic, and of global Tate duality statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside.lean

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

theorem NumberField.AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).FiniteIndex := by sorry
