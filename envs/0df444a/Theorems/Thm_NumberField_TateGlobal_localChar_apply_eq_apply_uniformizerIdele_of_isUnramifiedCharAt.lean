-- Prove2me | Theorems.Thm_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt
-- name    : NumberField.TateGlobal.localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/77bcc228-d0dd-5655-a292-e570a9daa50e
-- title:
--   Unramified local character agrees at any uniformizer
-- statement:
--   Let $K$ be a number field, $\chi\colon (\mathbf{A}_K)^\times \to \mathbb{C}^\times$ a group homomorphism from the units of the adele ring of $\mathcal{O}_K$ in $K$ to $\mathbb{C}^\times$, and $v$ a height-one prime of $\mathcal{O}_K$. Write `localChar` $\chi$ $v$ for the composite of $\chi$ with the homomorphism $(K_v)^\times \to (\mathbf{A}_K)^\times$ that sends a local unit $t$ to the idele whose component at $v$ is $t$, whose components at the other finite places are $1$, and whose infinite component is $1$. Assume $\chi$ is unramified at $v$ in the sense of `IsUnramifiedCharAt`: for every unit $t$ of the completion $K_v$ such that both $t$ and $t^{-1}$ lie in the valuation ring $\mathcal{O}_v$, one has `localChar` $\chi$ $v$ $t = 1$. Let $\varpi$ be a unit of $K_v$ whose valuation equals the image of $-1 \in \mathbb{Z}$ under `Multiplicative.ofAdd`, i.e. $\varpi$ is a uniformizer. Then `localChar` $\chi$ $v$ $\varpi$ equals $\chi$ evaluated at `uniformizerIdele` $K$ $v$, the idele built in the same way from the chosen uniformizer `uniformizerUnit` of $K_v$.
--
--   This is the standard fact that an unramified quasi-character of a local field is determined by its value at a uniformizer, in the form needed to compare local factors written with an arbitrary uniformizer at $v$ with those written with the fixed choice. It is used in the analysis of the Euler product of the global zeta function of an idele class character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical

theorem NumberField.TateGlobal.localChar_apply_eq_apply_uniformizerIdele_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (hχ : IsUnramifiedCharAt χ v)
    (ϖ : (v.adicCompletion K)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) :
    localChar χ v ϖ = χ (uniformizerIdele K v) := by sorry
