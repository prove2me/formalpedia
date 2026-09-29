-- Prove2me | Theorems.Thm_ModularForm_span_frickeRational_E4_pow_E6_pow_eq_top
-- name    : ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5be686be-a81f-5fbb-ae90-5c11d7c0a66b
-- title:
--   Rational fractions in j and Fricke functions span M_k(Γ)
-- statement:
--   Let $N\ge 1$. Let $L$ assign to each $\tau\in\mathfrak H$ a period pair with $\omega_1=\tau$, $\omega_2=1$; let $W$ be given by $W_v(\tau)=(2\pi i)^{-2}\,\wp_{L(\tau)}\!\big((\tilde v_0\tau+\tilde v_1)/N\big)$ for $v\in(\mathbb Z/N)^2$, where $\tilde v_i$ denotes the canonical lift to $\{0,\dots,N-1\}$; let $\mathrm{fricke}_v(\tau)=-\big(E_4(\tau)E_6(\tau)/\Delta(\tau)\big)\,W_v(\tau)/2592$ and $jf(\tau)=E_4(\tau)^3/\Delta(\tau)$; let $K=\mathbb Q\big(e^{2\pi i/N}\big)$ as an intermediate field of $\mathbb C/\mathbb Q$. Let $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ contain $\Gamma(N)$, and let $k\in\mathbb Z$, $a,b,m\in\mathbb N$ satisfy $k+4a+6b=12m$. The assertion is that the $\mathbb C$-span of the set of weight-$k$ modular forms $f$ for $\Gamma$ (regarded as a subgroup of $\mathrm{GL}_2(\mathbb R)$) consisting of those $f$ for which there exist polynomials $P,Q$ in commuting variables indexed by $\mathrm{Option}\,\{v\in(\mathbb Z/N)^2: v\neq 0\}$, all of whose coefficients lie in $K$, such that the function obtained from $Q$ by substituting $jf$ for the distinguished variable and $\mathrm{fricke}_v$ for the variable $v$ is not identically zero and such that $f(\tau)E_4(\tau)^aE_6(\tau)^b\,Q(jf,\mathrm{fricke})(\tau)=\Delta(\tau)^m\,P(jf,\mathrm{fricke})(\tau)$ for all $\tau\in\mathfrak H$, is the whole space $\top$.
--
--   This is the modular-form form of Shimura's rationality theorem for modular functions of level $N$: every weight-$k$ form on a group containing $\Gamma(N)$ is a $\mathbb C$-combination of forms whose companion $fE_4^aE_6^b/\Delta^m$ is a $\mathbb Q(\zeta_N)$-rational fraction in $j$ and the Fricke functions. It feeds the construction of bases of spaces of forms on $\Gamma_1(N)$ whose $q$-expansion coefficients lie in $\mathbb Q(\zeta_N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex Real UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma N ≤ Γ)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k |
      ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        (∀ mo, P.coeff mo ∈ K) ∧ (∀ mo, Q.coeff mo ∈ K) ∧
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) Q τ =
          ModularForm.discriminant τ ^ m *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke v.1) P τ} = ⊤ := by sorry
