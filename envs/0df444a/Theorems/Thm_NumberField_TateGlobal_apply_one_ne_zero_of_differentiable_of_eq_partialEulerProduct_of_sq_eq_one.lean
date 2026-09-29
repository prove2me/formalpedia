-- Prove2me | Theorems.Thm_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one
-- name    : NumberField.TateGlobal.apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8eb44ca6-a7fe-55a0-b6cf-9c9ea9999398
-- title:
--   Non-vanishing at s=1 for a quadratic idele class character
-- statement:
--   Let $K$ be a number field and let $\chi\colon \mathbb{A}_K^\times \to \mathbb{C}^\times$ be a group homomorphism from the units of the adele ring of $\mathcal{O}_K$ in $K$ to $\mathbb{C}^\times$, subject to: `IsIdeleClassChar`, i.e. $\chi$ kills the image of $K^\times$ under the diagonal embedding, so that $\chi(u)=1$ for every $u \in K^\times$; continuity of $\chi$; `IsUnitaryChar`, i.e. $|\chi(x)| = 1$ for every idele unit $x$; $\chi^2 = 1$; and $\chi \neq 1$. Let $T$ be a finite set of height-one primes of $\mathcal{O}_K$, and let $L\colon \mathbb{C} \to \mathbb{C}$ be differentiable on all of $\mathbb{C}$ and such that, for every $s$ with $\operatorname{Re} s > 1$, $$L(s) = \prod_{v \notin T}\bigl(1 - c_v\,(\mathrm{N}v)^{-s}\bigr)^{-1},$$ the product being the topological product over the subtype of primes not in $T$, where $\mathrm{N}v$ is the absolute norm of the ideal $v$, and where $c_v = \chi(\varpi_v)$ if $\chi$ is unramified at $v$ in the sense of `IsUnramifiedCharAt` — the local character $t \mapsto \chi$ of the idele which is $t$ at $v$ and $1$ elsewhere is trivial on those $t \in (K_v)^\times$ with $t$ and $t^{-1}$ both in the valuation ring — and $c_v = 0$ otherwise; here $\varpi_v$ is `uniformizerIdele`, the idele whose $v$-component is a uniformiser of $K_v$ and whose other components are $1$. The conclusion is $L(1) \neq 0$.
--
--   This is the non-vanishing at the edge of the critical strip for a quadratic (order-dividing-two) Hecke character, in the form needed here: the entire continuation $L$ of the Euler product away from a finite set $T$ of primes is taken as a hypothesis, and the assertion is that it does not vanish at $s = 1$. It is used by [`NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar`](thm.html#NumberField.TateGlobal.not_tendsto_partialEulerProduct_nhds_zero_of_isUnitaryChar), the case that the comparison with $\zeta_K$ through $\chi^2$ cannot reach.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal AutomorphicForm
open scoped Classical in

theorem NumberField.TateGlobal.apply_one_ne_zero_of_differentiable_of_eq_partialEulerProduct_of_sq_eq_one (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLE : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    L 1 ≠ 0 := by sorry
