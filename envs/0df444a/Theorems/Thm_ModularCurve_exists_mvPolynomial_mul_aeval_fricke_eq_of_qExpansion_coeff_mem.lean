-- Prove2me | Theorems.Thm_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem
-- name    : ModularCurve.exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/1ee56bf0-39ce-5bab-b809-25b996df57bb
-- title:
--   Descent by Fourier coefficients to K(j,fᵥ)
-- statement:
--   Let $N\ge 1$ be a natural number. The Weierstrass data are given as parameters with defining hypotheses: a family $L$ of period pairs with $(L\tau).\omega_1=\tau$ and $(L\tau).\omega_2=1$ for every $\tau$ in the upper half-plane; a family $W$ indexed by $v\in(\mathbb{Z}/N)^2$ with $W_v(\tau)=(2\pi i)^{-2}\,\wp\bigl(L\tau;\,(\tilde v_0\tau+\tilde v_1)/N\bigr)$, where $\tilde v_i$ denotes the least non-negative residue; the Fricke family $\mathit{fricke}_v(\tau)=-\tfrac{1}{2592}\,\bigl(E_4(\tau)E_6(\tau)/\Delta(\tau)\bigr)\,W_v(\tau)$; and $\mathit{jf}(\tau)=E_4(\tau)^3/\Delta(\tau)$. Let $K$ be the intermediate field $\mathbb{Q}\bigl(e^{2\pi i/N}\bigr)$ of $\mathbb{C}/\mathbb{Q}$. Let $m$ be a natural number and $G$ a function on the upper half-plane which is holomorphic (differentiable for the complex model on the half-plane), satisfies $G(\gamma\cdot\tau)=G(\tau)$ for all $\gamma\in\Gamma(N)$ and all $\tau$, is such that $\tau\mapsto G(\alpha\cdot\tau)\,\Delta(\tau)^m$ is bounded as $\operatorname{Im}\tau\to\infty$ for every $\alpha\in\mathrm{SL}_2(\mathbb{Z})$, and is such that every coefficient of the level-$N$ $q$-expansion of $G\cdot\Delta^m$ lies in $K$. Then there exist polynomials $P,Q$ over $K$ in variables indexed by $\mathrm{Option}\,\{v\in(\mathbb{Z}/N)^2: v\ne 0\}$ such that, evaluating the variables at $\mathit{jf}$ (for `none`) and at $\mathit{fricke}_v$ (for $v\ne 0$) after mapping coefficients into $\mathbb{C}$, the value of $Q$ is not the zero function on the upper half-plane, and $G$ times the value of $Q$ equals the value of $P$.
--
--   This is the rationality descent for the modular function field of level $N$ (Shimura's Proposition 6.9) in the case of functions holomorphic on the upper half-plane: a $\Gamma(N)$-invariant function with $\mathbb{Q}(\zeta_N)$-rational Fourier coefficients is a fraction, with coefficients in $\mathbb{Q}(\zeta_N)$, of polynomials in $j$ and the Fricke functions of level $N$. It is used by [`ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`](thm.html#ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant), on the way to the arithmetic of modular curves used in the modularity arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem
    (N : ℕ) [NeZero N]
    (L : UpperHalfPlane → PeriodPair)
    (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), W v τ =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : UpperHalfPlane), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : UpperHalfPlane → ℂ)
    (hjf : ∀ τ : UpperHalfPlane, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : UpperHalfPlane, G (γ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hcoeff : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K) :
    ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K,
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0 ∧
      G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) =
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ)) := by sorry
