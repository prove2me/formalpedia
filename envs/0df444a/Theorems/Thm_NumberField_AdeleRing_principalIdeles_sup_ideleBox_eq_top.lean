-- Prove2me | Theorems.Thm_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top
-- name    : NumberField.AdeleRing.principalIdeles_sup_ideleBox_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/6073b010-dd79-5ba7-9012-f7ab64b8a460
-- title:
--   Principal idèles and an idèle box exhaust the idèle group
-- statement:
--   Let $E$ be a number field, with ring of integers $\mathcal O_E$, and let $S \subseteq S'$ be finite sets of height-one primes of $\mathcal O_E$. Assume that the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) of $(\mathbb A_E)^\times$, namely the image of $E^\times$ under the map induced by $E \to \mathbb A_E$, together with [`NumberField.AdeleRing.unitIdelesOutside`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) at $S$ — the idèle units $y$ such that for every $v \notin S$ both the $v$-component of the finite part of $y$ and that of $y^{-1}$ lie in $\mathcal O_v$ — generate all of $(\mathbb A_E)^\times$. Let $H = (H_v)_v$ be a family of subgroups $H_v \le (E_v)^\times$, one for each height-one prime, with $H_v = (E_v)^\times$ for all $v \in S$, and assume the following surjectivity hypothesis: for every family $(x_v)_v$ of local units with $\mathrm{v}(x_v) = 1$ for all $v \in S' \setminus S$, there is $s \in E^\times$ with $v$-valuation $1$ at every $v \notin S$ such that $x_v s^{-1} \in H_v$ for all $v \in S' \setminus S$. Then the principal idèles together with [`NumberField.AdeleRing.ideleBox`](def/NumberField_IdeleBox.html#L126) at $S'$, $H$ and the full group at each infinite place — the idèle units $x$ whose finite part has $v$-component in $H_v$ for $v \in S'$ and has both its $v$-component and that of $x^{-1}$ integral for $v \notin S'$, with no condition at the infinite places — generate $(\mathbb A_E)^\times$.
--
--   This is the bookkeeping step in the algebraic proof of the second inequality of global class field theory: passing from the statement that $E^\times$ and the idèles that are units outside $S$ fill the idèle group to the same statement for a smaller box, cut out on an enlarged set $S'$ by prescribed local subgroups $H_v$, once $S$-units surject onto the relevant local quotients at the places of $S' \setminus S$. It is used in [`NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom`](thm.html#NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_principalIdeles_sup_ideleBox_eq_top.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_IdeleBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.AdeleRing.principalIdeles_sup_ideleBox_eq_top
    (E : Type*) [Field E] [NumberField E]
    (S S' : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (hSS' : S ⊆ S')
    (hS : M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers E) E ↑S = ⊤)
    (H : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → Subgroup (v.adicCompletion E)ˣ)
    (hH : ∀ v ∈ S, H v = ⊤)
    (hsurj : ∀ x : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → (v.adicCompletion E)ˣ,
      (∀ v ∈ S', v ∉ S → Valued.v ((x v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1) →
      ∃ s : Eˣ, (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S →
          v.valuation E (s : E) = 1) ∧
        ∀ v ∈ S', v ∉ S →
          x v * (Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) s)⁻¹ ∈ H v) :
    M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.ideleBox (NumberField.RingOfIntegers E) E ↑S' H ⊤ = ⊤ := by sorry
