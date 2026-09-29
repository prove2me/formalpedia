-- Prove2me | Theorems.Thm_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow
-- name    : NumberField.TateGlobal.differentiableOn_tprod_eulerFactor_of_norm_le_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/e476c383-283d-5c26-b9bd-de97b4935e87
-- title:
--   Convergence and holomorphy of a partial degree-two Euler product
-- statement:
--   Let $F$ be a number field, $S$ a finite set of height-one primes of $\mathcal{O}_F$, and $\chi\colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ a multiplicative character of the ideles. For a prime $v$ write $\varpi_v$ for the idele `uniformizerIdele F v`, whose infinite component is $1$, whose $v$-component is the image of a uniformizer of $\mathcal{O}_F$ at $v$ in $F_v$, and whose other finite components are $1$, and write $Nv =$ `Ideal.absNorm v.asIdeal`. Let $a, b$ be complex-valued functions on the primes and let $\tau, \kappa, \sigma_0$ be reals, subject to: $\|\chi(\varpi_v)\| \le (Nv)^{\tau}$ for all $v \notin S$; $\kappa \ge 0$ and $\|a_v\| \le (Nv)^{\kappa}$, $\|b_v\| \le (Nv)^{\kappa}$ for all $v \notin S$; and $\kappa + \tau + 4 \le \sigma_0$. For $v \notin S$ put $P_v(X) = 1 - \chi(\varpi_v) a_v X + \chi(\varpi_v)^2 b_v X^2$ if `IsUnramifiedCharAt χ v` holds, that is if $\chi$ sends to $1$ every idele which is $1$ outside $v$ and whose $v$-component is a unit $t$ of $F_v$ with both $t$ and $t^{-1}$ in the valuation ring of $F_v$, and $P_v(X) = 1$ otherwise. Then: for every $s$ with $\operatorname{Re} s > \sigma_0$ the family $\bigl(P_v((Nv)^{-s})^{-1}\bigr)_{v \notin S}$ has unconditional product equal to $\prod'_{v \notin S} P_v((Nv)^{-s})^{-1}$; and the function $s \mapsto \prod'_{v \notin S} P_v((Nv)^{-s})^{-1}$ is complex differentiable on the half-plane $\{s : \operatorname{Re} s > \sigma_0\}$.
--
--   This is the standard absolute-convergence and holomorphy statement for a partial degree-two Euler product with polynomially bounded local data, the half-plane $\operatorname{Re} s > \kappa + \tau + 4$ being a crude but sufficient abscissa. It is used to put the partial standard $L$-function attached to a Hecke eigenfunction on $\mathrm{GL}_2$, and its analogue for characters induced from a quadratic extension in the Langlands–Tunnell step, on a half-plane where the Euler product converges and defines a holomorphic function; the proof reduces to the degree-one statement [`NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one`](thm.html#NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow.lean

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.TateGlobal IsDedekindDomain AutomorphicForm Polynomial

open scoped Classical in

theorem NumberField.TateGlobal.differentiableOn_tprod_eulerFactor_of_norm_le_rpow
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (a b : HeightOneSpectrum (𝓞 F) → ℂ)
    (τ : ℝ)
    (hτ : ∀ v ∉ S, ‖((χ (uniformizerIdele F v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ)
    (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ‖a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (σ₀ : ℝ) (hσ₀ : κ + τ + 4 ≤ σ₀) :
    (∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
        (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
              + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        ((if IsUnramifiedCharAt χ v.1
          then C 1 - C (((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * a v.1) * X
            + C ((((χ (uniformizerIdele F v.1)) ^ 2 : ℂˣ) : ℂ) * b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
      {s : ℂ | σ₀ < s.re} := by sorry
