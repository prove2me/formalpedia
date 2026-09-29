-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_integrable_norm_mul_ideleNorm_rpow_of_valuation_of_prod_norm_pow_mul_le
-- name    : NumberField.TateGlobal.exists_forall_integrable_norm_mul_ideleNorm_rpow_of_valuation_of_prod_norm_pow_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/19d26e11-f5dc-5fbf-bf5f-a7c73ccec1cc
-- title:
--   Integrability of tempered idele functions against ‖·‖^σ
-- statement:
--   Let $F$ be a number field, and equip the idele group $\mathbb{A}_F^\times$ (the unit group of the adele ring of $\mathcal{O}_F$ in $F$) with a measurable structure that is the Borel structure of its topology, and with a Haar measure $\nu$. Let $W\colon\mathbb{A}_F^\times\to\mathbb{C}$ be almost everywhere strongly measurable for $\nu$, and let $c\colon\mathrm{Spec}^1(\mathcal{O}_F)\to\mathbb{Z}$ be a family of integers indexed by the nonzero primes of $\mathcal{O}_F$ which vanishes outside some finite set $S$ of primes. Assume the support condition: $W(b)=0$ for every idele $b$ such that at some prime $v$ the $v$-adic valuation of the finite component of $b$ at $v$ exceeds $\mathrm{exp}(c_v)$, the image of $c_v$ in $\mathbb{Z}_{m0}$. Assume further that there is a natural number $M$ with the property that for every family of natural numbers $(m_w)_{w\mid\infty}$ indexed by the infinite places of $F$ there exists a real constant $C$ with $$\Big(\prod_{w\mid\infty}\|b_w\|^{m_w}\Big)\,|W(b)|\;\le\;C\,\max\big(\|b\|,\|b\|^{-1}\big)^{M}$$ for all ideles $b$, where $b_w$ denotes the component of the archimedean part of $b$ at $w$ and $\|b\|$ is the idele norm, defined as the real number underlying the distributive Haar character of the scaling action of $b$ on the adele ring. Then there exists $\sigma_1\in\mathbb{R}$ such that for every real $\sigma>\sigma_1$ the function $b\mapsto |W(b)|\,\|b\|^{\sigma}$ is $\nu$-integrable.
--
--   This is the convergence half of the theory of global zeta integrals in the style of Tate's thesis: a function on the ideles whose finite-place support is bounded and whose archimedean decay is tempered uniformly in the archimedean weights has its zeta integral absolutely convergent in a right half-plane. It supplies the half-plane convergence used for integrability of zeta integrands of Whittaker coefficients and for the integrability estimates in the cubic-induction step of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_integrable_norm_mul_ideleNorm_rpow_of_valuation_of_prod_norm_pow_mul_le.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal MeasureTheory

theorem NumberField.TateGlobal.exists_forall_integrable_norm_mul_ideleNorm_rpow_of_valuation_of_prod_norm_pow_mul_le
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (W : (AdeleRing (𝓞 F) F)ˣ → ℂ) (hW : AEStronglyMeasurable W ν)
    (c : HeightOneSpectrum (𝓞 F) → ℤ) (hc : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, c v = 0)
    (hsupp : ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∃ v : HeightOneSpectrum (𝓞 F), WithZero.exp (c v) < Valued.v (((b : AdeleRing (𝓞 F) F).2) v)) → W b = 0)
    (M : ℕ)
    (hdec : ∀ m : InfinitePlace F → ℕ, ∃ C : ℝ, ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∏ w : InfinitePlace F, ‖((b : AdeleRing (𝓞 F) F).1 w)‖ ^ m w) * ‖W b‖
        ≤ C * max (ideleNorm F b) (ideleNorm F b)⁻¹ ^ M) :
    ∃ σ₁ : ℝ, ∀ σ : ℝ, σ₁ < σ → Integrable (fun b => ‖W b‖ * ideleNorm F b ^ σ) ν := by sorry
