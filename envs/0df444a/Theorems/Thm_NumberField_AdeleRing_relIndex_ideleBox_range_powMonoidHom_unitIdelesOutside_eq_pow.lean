-- Prove2me | Theorems.Thm_NumberField_AdeleRing_relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
-- name    : NumberField.AdeleRing.relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/2c161319-971f-555c-9a70-c9e4c9aa83ef
-- title:
--   Index p^{2(|S|+r₁+r₂)} of the local p-th power idèle box
-- statement:
--   Let $K$ be a number field, $p$ a prime, and assume that the set of primitive $p$-th roots of unity in $K$ is nonempty, i.e. $K$ contains a primitive $p$-th root of unity. Let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$ such that every $v$ whose prime ideal contains $p$ belongs to $S$. Consider the subgroup [`NumberField.AdeleRing.ideleBox`](def/NumberField_IdeleBox.html#L126) of $(\mathbb{A}_K)^\times$ attached to $S$ and to the local families $H_v =$ image of the $p$-th power map on $(K_v)^\times$ for finite $v$ and $H_w =$ image of the $p$-th power map on $(K_w)^\times$ for infinite $w$: it consists of the adelic units $x$ whose finite part satisfies, first, that for each $v \in S$ the $v$-component of the finite part is a $p$-th power in $(K_v)^\times$, and second, that for each $v \notin S$ both the $v$-component of $x$ and of $x^{-1}$ lie in the valuation ring $\mathcal{O}_v$, and whose component at each infinite place $w$ is a $p$-th power in $(K_w)^\times$. Let [`NumberField.AdeleRing.unitIdelesOutside`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) be the subgroup of adelic units whose finite part is integral together with its inverse at every $v \notin S$ (no condition at $S$ or at the infinite places). The assertion is that the relative index of the idèle box in this group equals $p^{2(|S| + \#\{\text{infinite places of } K\})}$, that is, $p^{2(|S| + r_1 + r_2)}$.
--
--   This is the computation of the index of the group of local $p$-th powers inside the $S$-idèles, for $S$ containing all places above $p$ and for $K$ containing $\mu_p$; it is the 'first index' entering the second inequality of Kummer-theoretic global duality arguments. It is used in the construction of a Galois extension on which prescribed idelic conditions hold, via [`NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top`](thm.html#NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow.lean

import Mathlib
import Definitions.Def_NumberField_IdeleBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.AdeleRing.relIndex_ideleBox_range_powMonoidHom_unitIdelesOutside_eq_pow
    {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p K).Nonempty)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ v.asIdeal → v ∈ S) :
    (NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers K) K (↑S)
        (fun v => (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)
        (fun w => (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range)).relIndex
      (NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers K) K (↑S))
      = p ^ (2 * (S.card + Fintype.card (NumberField.InfinitePlace K))) := by sorry
