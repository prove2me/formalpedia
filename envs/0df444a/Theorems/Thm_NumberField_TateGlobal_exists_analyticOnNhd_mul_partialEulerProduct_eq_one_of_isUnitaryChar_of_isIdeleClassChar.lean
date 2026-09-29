-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
-- name    : NumberField.TateGlobal.exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8d00d0f5-3511-59f1-9bc9-074ad1f00df9
-- title:
--   Non-vanishing of partial Hecke L-functions on Re w ≥ 1
-- statement:
--   Let $F$ be a number field, $S$ a finite set of nonzero prime ideals of the ring of integers $\mathcal{O}_F$, and let $\varpi$ assign to every such prime $v$ a unit $\varpi_v$ of the completion $F_v$ whose valuation equals $\mathrm{ofAdd}(-1)$, i.e. a uniformiser. Let $\chi$ be a monoid homomorphism from the group of units of the adele ring of $F$ to $\mathbb{C}^\times$ which is continuous, unitary in the sense that $\lVert\chi(x)\rVert = 1$ for every idele unit $x$, and trivial on principal ideles, i.e. $\chi(u) = 1$ for every $u \in F^\times$ mapped into the ideles. Then there are an open set $U \subseteq \mathbb{C}$ containing the closed half-plane $\{w : 1 \le \operatorname{Re} w\}$ and a function $P : \mathbb{C} \to \mathbb{C}$ analytic on a neighbourhood of each point of $U$, such that for every $w$ with $\operatorname{Re} w > 1$,
--   $$P(w) \cdot \prod_{v \notin S} \bigl(1 - \chi_v(\varpi_v)\, N(v)^{-w}\bigr)^{-1} = 1 .$$
--   Here the product is the unconditional infinite product over the primes not in $S$, $N(v)$ denotes the absolute norm of $v$, and $\chi_v$ is `localChar`, the character of $F_v^\times$ obtained by composing $\chi$ with the map sending $t \in F_v^\times$ to the idele unit that is $t$ at $v$, $1$ at all other finite places, and $1$ at the infinite places. In particular the product is nonzero on $\operatorname{Re} w > 1$ and its reciprocal extends analytically past the line $\operatorname{Re} w = 1$.
--
--   This is the statement that the reciprocal of the partial Hecke $L$-function $L^S(w,\chi)$ of a unitary idele class character continues holomorphically to a neighbourhood of the closed half-plane $\operatorname{Re} w \ge 1$; its content beyond the region of absolute convergence is the absence of zeros of $L^S(\,\cdot\,,\chi)$ on the line $\operatorname{Re} w = 1$, in the tradition of Hadamard–de la Vallée Poussin as extended by Hecke. It is used in the analytic continuation of the Bruhat–Eisenstein series and of the Weyl intertwining integral, where the inverse of such an Euler product appears as a normalising factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.exists_analyticOnNhd_mul_partialEulerProduct_eq_one_of_isUnitaryChar_of_isIdeleClassChar
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) :
    ∃ (U : Set ℂ) (P : ℂ → ℂ), IsOpen U ∧ {w : ℂ | 1 ≤ w.re} ⊆ U ∧ AnalyticOnNhd ℂ P U ∧
      ∀ w : ℂ, 1 < w.re →
        P w * (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))⁻¹) = 1 := by sorry
