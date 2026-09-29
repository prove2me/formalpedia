-- Prove2me | Theorems.Thm_NumberField_TateGlobal_isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
-- name    : NumberField.TateGlobal.isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4fa063b9-d388-5667-8b30-2c45e5dac2f2
-- title:
--   Unramifiedness of μ∘ N_{M/E} at an unramified prime
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra, let $\mu:\mathbb{A}_E^\times\to\mathbb{C}^\times$ be a group homomorphism from the ideles of $E$ (the units of `AdeleRing (𝓞 E) E`) to $\mathbb{C}^\times$, and let $w$ be a height-one prime of $\mathcal{O}_M$ with $v=w\cap\mathcal{O}_E$ its prime below, written `w.under (𝓞 E)`. Assume the ramification index $e(w\mid v)$, in the sense of `Ideal.ramificationIdx'` for the pair $(v,w)$, equals $1$. Then the character $\mu$ composed with the idelic norm attached to `genuineBaseChange E M` — that is, the map on unit groups induced by the algebra norm $\mathbb{A}_M\to\mathbb{A}_E$ for the algebra structure coming from the canonical ring homomorphism $\mathbb{A}_E\to\mathbb{A}_M$, whose accompanying identification is $\mathbb{A}_E\otimes_E M\cong\mathbb{A}_M$ — is unramified at $w$ if and only if $\mu$ is unramified at $v$. Here a character $\chi$ is unramified at a finite prime $u$ when its local component at $u$, namely $\chi$ composed with the inclusion of $(\widehat{K_u})^\times$ into the ideles concentrated at $u$, sends to $1$ every unit $t$ of the completion such that both $t$ and $t^{-1}$ lie in the valuation ring at $u$.
--
--   This is the standard compatibility of ramification of idele class characters with the norm map in a place that is unramified in $M/E$, in the form needed to transfer unramifiedness conditions between a number field and an extension. It is used in the construction of automorphic forms obtained by composing a character with the idelic norm, and in the cubic-induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one.lean

import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal M4aHerbrand.GenuineDescent

theorem NumberField.TateGlobal.isUnramifiedCharAt_comp_idelicNorm_genuineBaseChange_iff_of_ramificationIdx_eq_one
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 M))
    (he : Ideal.ramificationIdx' (w.under (𝓞 E)).asIdeal w.asIdeal = 1) :
    IsUnramifiedCharAt (μ.comp (genuineBaseChange E M).idelicNorm) w ↔
      IsUnramifiedCharAt μ (w.under (𝓞 E)) := by sorry
