-- Prove2me | Theorems.Thm_NumberField_TateGlobal_finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one
-- name    : NumberField.TateGlobal.finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/f4a3c9d0-8b0e-57b8-88a2-1ab0b3a8a16c
-- title:
--   Local components at -1 of a norm-composite idele character
-- statement:
--   Let $E$ and $K$ be number fields with $K$ an $E$-algebra, let $\chi \colon (\mathbb{A}_E)^\times \to \mathbb{C}^\times$ be a monoid homomorphism from the units of the adele ring `AdeleRing (𝓞 E) E` to $\mathbb{C}^\times$, and let $v$ be a height-one prime of $\mathcal{O}_E$. Here, for a character $\psi$ of the idele group and a height-one prime $w$, the local component `localChar ψ w` is the homomorphism $(K_w)^\times \to \mathbb{C}^\times$ obtained by sending a local unit $t$ to the idele whose $w$-component is $t$, whose other finite components are $1$ and whose infinite component is $1$, and then applying $\psi$; `primeFibre E K v` is the set of height-one primes $\mathfrak{P}$ of $\mathcal{O}_K$ with $\mathfrak{P}$ lying under $v$, i.e. $\mathfrak{P}.\mathrm{under}\,\mathcal{O}_E = v$; and `(genuineBaseChange E K).idelicNorm` is the map on unit groups induced by the algebra norm of $\mathbb{A}_K$ over $\mathbb{A}_E$ taken along the base-change ring homomorphism $\mathbb{A}_E \to \mathbb{A}_K$ of `genuineBaseChange`. The assertion is the equality of the (finitely supported) product over $w \in$ `primeFibre E K v` of the values at $-1$ of the local components of $\chi$ composed with this idelic norm with the value $\chi_v\bigl((-1)^{\,[K:E]}\bigr)$, where $[K:E]$ is `Module.finrank E K`.
--
--   This is the place-by-place compatibility of local components of a Hecke character with the idelic norm of an extension, evaluated at $-1$: the product over the places above $v$ collapses to the value of the local component at $v$ on $(-1)^{[K:E]}$, so that for odd degree it is simply $\chi_v(-1)$. It is used in the sign computation of the Rankin–Selberg assembly in the cubic case of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal M4aHerbrand.GenuineDescent LanglandsTunnell.RankinSelberg

theorem NumberField.TateGlobal.finprod_mem_primeFibre_localChar_comp_idelicNorm_apply_neg_one
    (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [Algebra E K]
    (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 E)) :
    ∏ᶠ w ∈ primeFibre E K v, localChar (χ.comp (genuineBaseChange E K).idelicNorm) w (-1) =
      localChar χ v ((-1) ^ Module.finrank E K) := by sorry
