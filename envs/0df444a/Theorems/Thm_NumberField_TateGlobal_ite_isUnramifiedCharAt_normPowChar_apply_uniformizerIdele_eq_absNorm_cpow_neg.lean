-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
-- name    : NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/70995ff2-8d2a-5cc2-b34b-2ef8011fbd60
-- title:
--   Unramified Euler coefficient of ‖·‖^{it} at v is Nv^{-it}
-- statement:
--   Let $K$ be a number field, $t$ a real number and $v$ a non-zero prime ideal of $\mathcal{O}_K$. Write $\|x\| =$ `ideleNorm`, the value at $x$ of the distributive Haar character of $\mathbb{A}_K$, and let `normPowChar K t` be the homomorphism $\mathbb{A}_K^\times \to \mathbb{C}^\times$ sending $x$ to $\|x\|^{it}$ (complex power of the positive real $\|x\|$ with exponent $i t$). Let `uniformizerIdele K v` be the idele whose archimedean component is $1$ and whose finite component is $1$ at every place other than $v$ and equal to the image of a uniformizer of $v$ at $v$. The assertion is that the quantity defined as $\|\varpi_v\|^{it}$ if `normPowChar K t` is unramified at $v$ — meaning that the induced homomorphism on $(K_v)^\times$, obtained by embedding a local unit at $v$ into the finite ideles and then into the ideles, is trivial on every $u$ with both $u$ and $u^{-1}$ in the valuation ring of $K_v$ — and as $0$ otherwise, equals $(N v)^{-it}$, where $Nv$ is the absolute norm `Ideal.absNorm v.asIdeal` regarded as a complex number and the power has exponent $-(i t)$. In particular the unramifiedness condition holds, so the gate is open.
--
--   This is the local computation behind the Euler factors of the norm-power character $\|\cdot\|^{it}$ in Tate's global theory: the character is everywhere unramified and its value on the uniformizer idele at $v$ is $Nv^{-it}$, so twisting by it shifts the argument of the partial Dedekind zeta function by $it$. It is used in the analytic continuation and growth estimates for intertwining integrals of induced sections and in the construction of entire Euler twists in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm
open scoped Classical in

theorem NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg (K : Type) [Field K] [NumberField K] (t : ℝ) (v : HeightOneSpectrum (𝓞 K)) :
    (if IsUnramifiedCharAt (normPowChar K t) v then ((normPowChar K t (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by sorry
