-- Prove2me | Theorems.Thm_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom
-- name    : NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/391aad9f-06ae-582d-ae30-705c97cd2fbe
-- title:
--   Local p-th powers away from S ∪ T are global
-- statement:
--   Let $E$ be a number field containing a primitive $p$-th root of unity for a prime $p$ (the set `primitiveRoots p E` is assumed nonempty), and let $S, T$ be finite sets of height-one primes of $\mathcal O_E =$ `NumberField.RingOfIntegers E`. Assume: (i) every $v$ whose prime ideal contains $p$ lies in $S$; (ii) the join, inside the unit group of the adele ring of $E$, of the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) (the image of $E^\times$ under the structure map) and of [`NumberField.AdeleRing.unitIdelesOutside`](def/IsDedekindDomain_FiniteUnitIdelesOutside.html#L51) at $S$ (the ideles $\delta$ such that for every $v \notin S$ both the $v$-component of the finite part of $\delta$ and that of $\delta^{-1}$ lie in the valuation ring of $E_v$) is the whole group; (iii) for every family $x = (x_v)_v$ of local units, one at each finite place, with $\lvert x_v \rvert = 1$ for all $v \in T$ with $v \notin S$, there exists $s \in E^\times$ with $v(s) = 1$ for all $v \notin S$ and such that, for each $v \in T$ with $v \notin S$, the element $x_v \cdot s^{-1}$ is a $p$-th power in $E_v^\times$. Let finally $u \in E$ satisfy $v(u) = 1$ for every $v$ outside $S \cup T$, be a $p$-th power in $E_v$ for every $v \in S$, and be a $p$-th power in the completion $E_w$ for every real infinite place $w$ of $E$. Then $u = c^p$ for some $c \in E$.
--
--   This is the crux lemma of the algebraic proof of the second inequality of class field theory: an $(S \cup T)$-unit that is a local $p$-th power at the places of $S$ and at the real places is already a global $p$-th power. It feeds the computation of the index of the norm coset of the idele class group in the cyclic degree-$p$ case, used by [`NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots`](thm.html#NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots) and by [`NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top`](thm.html#NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom
    (E : Type*) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hζ : (primitiveRoots p E).Nonempty)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)))
    (hSp : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E),
      (p : NumberField.RingOfIntegers E) ∈ v.asIdeal → v ∈ S)
    (hS : M4aHerbrand.principalIdeles (NumberField.RingOfIntegers E) E ⊔
      NumberField.AdeleRing.unitIdelesOutside (NumberField.RingOfIntegers E) E ↑S = ⊤)
    (hsurj : ∀ x : (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) → (v.adicCompletion E)ˣ,
      (∀ v ∈ T, v ∉ S → Valued.v ((x v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1) →
      ∃ s : Eˣ, (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S →
          v.valuation E (s : E) = 1) ∧
        ∀ v ∈ T, v ∉ S → ∃ c : (v.adicCompletion E)ˣ,
          x v * (Units.map (algebraMap E (v.adicCompletion E) : E →* v.adicCompletion E) s)⁻¹ = c ^ p)
    (u : E) (hu : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E), v ∉ S → v ∉ T →
      v.valuation E u = 1)
    (huS : ∀ v ∈ S, ∃ b : v.adicCompletion E, algebraMap E (v.adicCompletion E) u = b ^ p)
    (huinf : ∀ w : NumberField.InfinitePlace E, w.IsReal → ∃ b : w.Completion, algebraMap E w.Completion u = b ^ p) :
    ∃ c : E, u = c ^ p := by sorry
