-- Prove2me | Theorems.Thm_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one
-- name    : NumberField.Idele.exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/368a805d-2897-57ef-99f2-50c4422812ad
-- title:
--   Splicing an idele from prescribed local components
-- statement:
--   Let $K$ be a number field (a field with the number-field structure), let $S$ and $T$ be finite sets of height-one primes of the ring of integers $\mathcal{O}_K$, let $z$ be a unit of the adele ring $\mathbb{A}_K$ of $K$, and let $x$ assign to every height-one prime $v$ a unit $x_v$ of the completion $K_v$. Here an element of $\mathbb{A}_K$ is a pair consisting of an infinite component (first coordinate) and a finite adele (second coordinate), the latter being evaluated at each $v$. The assertion is that there exists a unit $z^{*}$ of $\mathbb{A}_K$ such that: its infinite component equals that of $z$; for every $v \in S$ the $v$-component of its finite part equals the $v$-component of the finite part of $z$; for every $v \in T$ with $v \notin S$ the $v$-component of its finite part equals the image in $K_v$ of the prescribed unit $x_v$; and for every height-one prime $v$ lying neither in $S$ nor in $T$ the $v$-component of its finite part equals $1$. Nothing is prescribed about the values $x_v$ for $v \notin T \setminus S$, and no disjointness of $S$ and $T$ is assumed.
--
--   This is the elementary splicing statement for the restricted product describing the idele group: an idele may be modified so as to keep the archimedean part and the components on a finite set $S$, to carry prescribed local units on a further finite set $T$ away from $S$, and to be trivial at all remaining finite places. It is used in the adelic manipulation of automorphic forms, being cited in [`AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero`](thm.html#AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero) to replace an idele by a spliced representative.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.Idele.exists_fst_eq_and_snd_eq_of_mem_and_snd_eq_of_mem_and_snd_eq_one
    (K : Type) [Field K] [NumberField K]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (z : (AdeleRing (𝓞 K) K)ˣ)
    (x : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) :
    ∃ zs : (AdeleRing (𝓞 K) K)ˣ,
      ((zs : AdeleRing (𝓞 K) K).1 = (z : AdeleRing (𝓞 K) K).1) ∧
      (∀ v ∈ S, (zs : AdeleRing (𝓞 K) K).2 v = (z : AdeleRing (𝓞 K) K).2 v) ∧
      (∀ v ∈ T, v ∉ S → (zs : AdeleRing (𝓞 K) K).2 v = ((x v : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → (zs : AdeleRing (𝓞 K) K).2 v = 1) := by sorry
