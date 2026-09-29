-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_transitionStable_family_one_ne_bot_of_odd_signClass
-- name    : LanglandsTunnell.CubicInduction.transitionStable_family_one_ne_bot_of_odd_signClass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/48346c33-a7b9-5776-bdfa-9ae323c08f05
-- title:
--   Odd sign classes: transition-stable families reach degree one
-- statement:
--   Fix real numbers $\sigma,\sigma_3$ and indices $b_0,c_0\in\mathrm{Fin}\,3$ with $b_0\neq 0$, $c_0\neq 0$, $b_0\neq c_0$ (so $\{0,b_0,c_0\}$ exhausts $\mathrm{Fin}\,3$), let $\nu:\mathrm{Fin}\,3\to\mathbb{C}$ satisfy $\nu_0=-\tfrac12+\sigma i$, $\nu_{b_0}=\tfrac12+\sigma i$, $\nu_{c_0}=\sigma_3 i$, let $\varepsilon:\mathrm{Fin}\,3\to\mathrm{Fin}\,2$ satisfy $\varepsilon_0\neq\varepsilon_{b_0}$, and let $S:\mathbb{N}\to$ (complex subspaces of $\mathbb{C}[x_0,x_1,x_2]$). Three operators are introduced by local definitions: $\Xi$ sends $\nu$ and $p$ to the $3\times 3$ matrix of polynomials whose diagonal entry at $c$ is $2(\nu_c+\delta_c)p$ with $\delta=(1,0,-1)$, and whose entry at $c\neq d$ is $-\bigl(x_{\max(c,d)}\,\partial_{\min(c,d)}p-x_{\min(c,d)}\,\partial_{\max(c,d)}p\bigr)$; $\mathrm{lower}_2(M)=\sum_{c,d}\partial_c\partial_d(M_{cd})$; and $\mathrm{lower}_1(M)=\sum_{a,b,c,d}\tfrac{(a-c)(c-d)(d-a)}{2}\,x_c\,\partial_b\partial_d(M_{ab})$, the index differences taken in $\mathbb{C}$ via $\mathrm{Fin}\,3\to\mathbb{N}\to\mathbb{C}$. Assume: (i) every $p\in S\ell$ is homogeneous of degree $\ell$ and harmonic, $\sum_i\partial_i^2p=0$; (ii) for all $\ell$, all $p\in S\ell$ and every sign vector $s:\mathrm{Fin}\,3\to\mathrm{Fin}\,2$ (the Lean binder here reuses the name $\sigma$), the substitution $x_a\mapsto(-1)^{s_a}x_a$ multiplies $p$ by $(-1)^{\sum_a(\varepsilon_a+\ell+\sum_b\varepsilon_b)s_a}$; (iii) for all $\ell$ and $p\in S\ell$, $\mathrm{lower}_2(\Xi\,\nu\,p)\in S(\ell-2)$ and $\mathrm{lower}_1(\Xi\,\nu\,p)\in S(\ell-1)$, with truncated subtraction of naturals; and (iv) $S\ell\neq\bot$ for some $\ell$. Then $S1\neq\bot$.
--
--   This is the descent step in the compact-picture analysis of the reducible principal series of $\mathrm{GL}_3(\mathbb{R})$ used on the Langlands–Tunnell side: starting from any non-trivial degree in a family of harmonic polynomial spaces of the given odd sign type that is stable under the two degree-lowering transitions attached to $\nu$, one reaches degree $1$. It relies on the degree $\ge 3$ injectivity of joint lowering recorded in [`LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le`](thm.html#LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le), and is in turn used by [`LanglandsTunnell.CubicInduction.exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable`](thm.html#LanglandsTunnell.CubicInduction.exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable) and [`LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package`](thm.html#LanglandsTunnell.CubicInduction.forall_apply_orthogonal_eq_zero_of_signIsotypic_odd_of_inducedPicture_package).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_transitionStable_family_one_ne_bot_of_odd_signClass.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.transitionStable_family_one_ne_bot_of_odd_signClass
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I)
    (ε : Fin 3 → Fin 2) (hodd : ε 0 ≠ ε b₀)
    (S : ℕ → Submodule ℂ (MvPolynomial (Fin 3) ℂ)) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (∀ ℓ, ∀ p : MvPolynomial (Fin 3) ℂ, p ∈ S ℓ →
            p.IsHomogeneous ℓ ∧ (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) →
    (∀ ℓ, ∀ p ∈ S ℓ, ∀ σ : Fin 3 → Fin 2,
        MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.C ((-1 : ℂ) ^ (σ a : ℕ)) * MvPolynomial.X a) p =
          MvPolynomial.C ((-1 : ℂ) ^ (∑ a : Fin 3, ((ε a : ℕ) + ℓ + ∑ b : Fin 3, (ε b : ℕ)) * (σ a : ℕ))) * p) →
    (∀ ℓ, ∀ p ∈ S ℓ, lower₂ (Ξ ν p) ∈ S (ℓ - 2) ∧ lower₁ (Ξ ν p) ∈ S (ℓ - 1)) →
    (∃ ℓ, S ℓ ≠ ⊥) → S 1 ≠ ⊥ := by sorry
