-- Prove2me | Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
-- name    : NumberField.AdelicFourier.fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/df630fb7-321e-5724-988b-9fb364a0f859
-- title:
--   Fourier transform of the dual lattice of mathcal Oᵥ
-- statement:
--   Let $F$ be a number field and $v$ a nonzero prime of its ring of integers $\mathcal{O}_F$, with associated completion $F_v$ and valuation ring $\mathcal{O}_v$ (the subring `v.adicCompletionIntegers F` of `v.adicCompletion F`). Equip $F_v$ with a measurable space structure that is its Borel structure, and let $\mu$ be an additive Haar measure on $F_v$. Let $\psi : F_v \to \mathbb{C}^{\times}$ be a continuous additive character which satisfies $\psi(z) = 1$ for every $z \in \mathcal{O}_v$ and which is not identically $1$ on $F_v$. Put $L := \{ y \in F_v : \psi(zy) = 1 \text{ for all } z \in \mathcal{O}_v \}$. The assertion is threefold: $L$ is open; $L$ is compact; and for every $w \in F_v$ the Fourier integral of the complex indicator function of $L$ against $\psi$ and $\mu$, namely $\int_{F_v} \psi(-(x w))\, \mathbf 1_L(x) \, d\mu(x)$ in the sense of the project's `fourierIntegral`, equals the real number $\mu(L)$, viewed as a complex number, times the value at $w$ of the complex indicator function of $\mathcal{O}_v$.
--
--   This is the local computation underlying Tate's self-duality at a finite place: for an unramified but nontrivial additive character $\psi$ of $F_v$, the set $L$ dual to $\mathcal{O}_v$ is a compact open fractional ideal, and the Fourier transform of $\mathbf 1_L$ is a multiple of $\mathbf 1_{\mathcal{O}_v}$. It is used in the construction of an adelic test function that is standard outside a finite set of places and has prescribed nonnegative integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one.lean

import Definitions.Def_NumberField_AdelicFourier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicFourier IsDedekindDomain MeasureTheory

theorem NumberField.AdelicFourier.fourierIntegral_indicator_setOf_forall_mem_adicCompletionIntegers_apply_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion F) ℂ) (hψ : Continuous ψ)
    (h0 : ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ z = 1)
    (h1 : ∃ z : v.adicCompletion F, ψ z ≠ 1) :
    IsOpen {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} ∧
    IsCompact {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} ∧
    ∀ w : v.adicCompletion F,
      fourierIntegral ψ μ
          ({y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1}.indicator
            fun _ => (1 : ℂ)) w =
        (μ.real {y : v.adicCompletion F | ∀ z : v.adicCompletion F, z ∈ v.adicCompletionIntegers F → ψ (z * y) = 1} : ℂ) *
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) w := by sorry
