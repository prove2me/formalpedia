-- Prove2me | Theorems.Thm_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational
-- name    : ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/b537ed49-0fa6-5b01-9da2-82e1455066b1
-- title:
--   q-expansion coefficients of Fricke-rational forms on Γ₁(N)
-- statement:
--   Fix $N\ge 1$ (a `NeZero N` instance) and data as follows. A family $L$ of period pairs with $(L\tau).\omega_1=\tau$ and $(L\tau).\omega_2=1$ for every $\tau$ in the upper half-plane, so that $L\tau$ presents the lattice $\mathbb{Z}\tau+\mathbb{Z}$; a function $W$ on $(\mathbb{Z}/N)^2\times\mathfrak{H}$ with $W_v(\tau)=(2\pi i)^{-2}\,\wp_{L\tau}\big((\tilde v_0\tau+\tilde v_1)/N\big)$, where $\tilde v_0,\tilde v_1$ are the canonical representatives in $\{0,\dots,N-1\}$; a function $\mathrm{fricke}$ with $\mathrm{fricke}_v(\tau)=-\big(E_4(\tau)E_6(\tau)/\Delta(\tau)\big)/2592\cdot W_v(\tau)$; a function $jf$ with $jf(\tau)=E_4(\tau)^3/\Delta(\tau)$; and an intermediate field $K$ of $\mathbb{C}/\mathbb{Q}$ equal to $\mathbb{Q}\big(e^{2\pi i/N}\big)$. Let $k\in\mathbb{Z}$, let $a,b,m\in\mathbb{N}$, let $f$ be a modular form of weight $k$ on $\Gamma_1(N)$, and let $P,Q$ be polynomials over $\mathbb{C}$ in variables indexed by $\mathrm{Option}\,\{v\in(\mathbb{Z}/N)^2 : v\neq 0\}$, all of whose coefficients lie in $K$. Write $\Phi$ for the evaluation of such a polynomial at the family of functions sending the base point to $jf$ and $v$ to $\mathrm{fricke}_v$. Assume $\Phi(Q)\neq 0$ in the ring of functions $\mathfrak{H}\to\mathbb{C}$, and assume the pointwise identity $f(\tau)\,E_4(\tau)^aE_6(\tau)^b\,\Phi(Q)(\tau)=\Delta(\tau)^m\,\Phi(P)(\tau)$ for all $\tau$. Then for every $n\in\mathbb{N}$ the $n$-th coefficient of the $q$-expansion of $f$ of period $1$ lies in $K$. No relation between $k$ and $a,b,m$ is assumed.
--
--   This is the passage from the field-theoretic form of $K$-rationality of a modular form on $\Gamma_1(N)$ — that a suitable weight-zero companion $fE_4^aE_6^b/\Delta^m$ be a $K$-rational fraction in $j$ and the Fricke functions of level $N$ — to rationality of its Fourier coefficients at the cusp $\infty$ with respect to $q=e^{2\pi i\tau}$, in arbitrary weight. It is applied by [`ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even`](thm.html#ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even) and [`CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even`](thm.html#CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even) to convert a spanning family of Fricke-rational forms into a basis whose $q$-expansion coefficients lie in $\mathbb{Q}(e^{2\pi i/N})$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational
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
    (k : ℤ) (a b m : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ mo, P.coeff mo ∈ K) (hQK : ∀ mo, Q.coeff mo ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) Q τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) P τ)
    (n : ℕ) :
    (UpperHalfPlane.qExpansion 1 ⇑f).coeff n ∈ K := by sorry
