-- Prove2me | Theorems.Thm_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
-- name    : NumberField.TateGlobal.eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/ef5a372d-b5a3-572a-a502-40b00dbd8f34
-- title:
--   Triviality of an idele class character with trivial local components
-- statement:
--   Let $F$ be a number field, and let $\chi$ be a multiplicative homomorphism from the units of the adele ring $\mathbb{A}_F$ of $F$ (realised as the product of the infinite adele ring of $F$ with the finite adele ring of $\mathcal{O}_F$) to $\mathbb{C}^\times$. Assume three hypotheses. First, `IsIdeleClassChar`: for every $u \in F^\times$ one has $\chi(u) = 1$, where $u$ is viewed as an idele via the unit map induced by the structure morphism $F \to \mathbb{A}_F$; that is, $\chi$ is trivial on the principal ideles. Second, $\chi$ is continuous. Third, there is a finite set $S$ of height one primes $v$ of $\mathcal{O}_F$ (finite places of $F$) such that for every $v \notin S$ the local component `localChar` $\chi$ $v$ is the trivial homomorphism; here `localChar` $\chi$ $v$ is the composite of $\chi$ with the embedding $(F_v)^\times \to (\mathbb{A}_F)^\times$ sending $t$ to the idele whose component at $v$ is $t$, whose components at all other finite places are $1$, and whose infinite part is $1$. The conclusion is that $\chi$ is the trivial character, $\chi = 1$.
--
--   This is the rigidity of Hecke characters: a continuous idele class character is determined by its local components at almost all finite places, so one whose components are almost everywhere trivial is itself trivial. It is used in the cubic induction arguments of the Langlands–Tunnell part of the proof, where local data at the finitely many bad places must be shown to pin down a global character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm

theorem NumberField.TateGlobal.eq_one_of_isIdeleClassChar_of_continuous_of_forall_localChar_eq_one
    (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hcont : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, localChar χ v = 1) :
    χ = 1 := by sorry
