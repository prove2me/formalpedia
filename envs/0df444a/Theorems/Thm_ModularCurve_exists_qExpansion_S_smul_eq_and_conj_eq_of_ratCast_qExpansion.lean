-- Prove2me | Theorems.Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion
-- name    : ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/572eb65b-b9e3-5691-90d0-8e0493f3d15e
-- title:
--   Shimura reciprocity at S for level N modular functions
-- statement:
--   Fix a positive integer $N$, a natural number $m$, and a function $G\colon\mathfrak H\to\mathbb C$ on the upper half-plane which is holomorphic (complex manifold differentiable for the standard chart on $\mathfrak H$), invariant under the congruence subgroup $\Gamma_1(N)$ in the sense that $G(g\cdot\tau)=G(\tau)$ for all $g\in\Gamma_1(N)$ and all $\tau$, and such that for every $\alpha\in SL_2(\mathbb Z)$ the product $(\tau\mapsto G(\alpha\cdot\tau))\cdot\Delta^m$ is bounded as $\operatorname{Im}\tau\to\infty$, where $\Delta$ is the discriminant cusp form. Assume further that every coefficient of the $q$-expansion of width $1$ of $G\cdot\Delta^m$ is the image of a rational number in $\mathbb C$. Let $\iota\colon\overline{\mathbb Q}\to\mathbb C$ be a ring homomorphism from an algebraic closure of $\mathbb Q$, and write $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. Then there is a sequence $(a_n)_{n\ge 0}$ in $\overline{\mathbb Q}$ such that, first, for every $n$ the $n$-th coefficient of the $q$-expansion of width $N$ of $(\tau\mapsto G(S\cdot\tau))\cdot\Delta^m$ equals $\iota(a_n)$; and second, for every $\mathbb Q$-algebra automorphism $\sigma$ of $\overline{\mathbb Q}$ and every natural number $c$ with $\sigma(\zeta)=\zeta^{c}$ for all $\zeta\in\overline{\mathbb Q}$ satisfying $\zeta^{N}=1$, and every $\gamma\in SL_2(\mathbb Z)$ whose entry $\gamma_{01}$ is $\equiv 0$ and whose entry $\gamma_{11}$ is $\equiv c$ modulo $N$, the $n$-th coefficient of the $q$-expansion of width $N$ of $(\tau\mapsto G(S\cdot\gamma\cdot\tau))\cdot\Delta^m$ equals $\iota(\sigma(a_n))$ for every $n$.
--
--   This is Shimura's reciprocity law specialised to the matrix $S$: the Fourier coefficients at $i\infty$ of $G\circ S$, for a $\Gamma_1(N)$-invariant modular function with rational expansion at $\infty$, are algebraic, and the action of $\sigma_c\colon\zeta_N\mapsto\zeta_N^{c}$ on them is realised geometrically by right translation by any $\gamma\equiv\operatorname{diag}(c^{-1},c)$ modulo $N$. It feeds the statement [`ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0`](thm.html#ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0), which transports the same rationality and Galois-equivariance to the Fricke involution and the $\Gamma_0(N)$-action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion (N : ℕ) [NeZero N]
    (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion N
        ((fun τ : UpperHalfPlane => G (ModularGroup.S • τ)) * ModularForm.discriminant ^ m)).coeff n =
          ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), ((γ 0 1 : ℤ) : ZMod N) = 0 → ((γ 1 1 : ℤ) : ZMod N) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N
            ((fun τ : UpperHalfPlane => G (ModularGroup.S • γ • τ)) *
              ModularForm.discriminant ^ m)).coeff n = ι (σ (a n)) := by sorry
