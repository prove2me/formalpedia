-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
-- name    : ModularCurve.JZero.exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/af16f96a-9993-5077-9c34-4ff1f67983a8
-- title:
--   p-adic Weil pairing on the Tate module of J₀(M)
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number. Write $J_0(M)$ for [`ModularCurve.JZero M`](def/ModularCurve_ArithmeticGalois.html#L115), the group of degree-zero divisors modulo principal divisors of the field `modularFunctionFieldBar M` (the base change to $\overline{\mathbb Q}$, inside Laurent series over $\overline{\mathbb Q}$, of the full modular function field of level $M$) over $\overline{\mathbb Q}$, and let $T_p J_0(M)$ be [`TateModule p (ModularCurve.JZero M)`](def/EllipticCurve_TateModule.html#L15): the group of sequences $x \colon \mathbb N \to J_0(M)$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ for all $n$, a module over $\mathbb Z_p$. The group $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, acts on $T_p J_0(M)$ componentwise through [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174), by $\mathbb Z_p$-linear endomorphisms. The assertion is that there exists a $\mathbb Z_p$-bilinear form $B \colon T_p J_0(M) \times T_p J_0(M) \to \mathbb Z_p$ (given as a $\mathbb Z_p$-linear map into the $\mathbb Z_p$-linear functionals) such that, first, $B(\sigma x, \sigma y) = \chi_p(\sigma)\,B(x,y)$ for every such $\sigma$ and all $x, y$, where $\chi_p(\sigma) \in \mathbb Z_p^\times \subseteq \mathbb Z_p$ is the value of `cyclotomicCharacter` at $p$ on the ring isomorphism underlying $\sigma$; and, second, $B$ separates points on each side: if $B(x,y) = 0$ for all $y$ then $x = 0$, and if $B(x,y) = 0$ for all $x$ then $y = 0$. No symmetry, alternating property or perfectness of $B$ is asserted.
--
--   This is the $p$-adic Weil pairing on the Tate module of the Jacobian of $X_0(M)$, packaged as a $\mathbb Z_p$-bilinear form with values in $\mathbb Z_p$ whose Galois similitude factor is the $p$-adic cyclotomic character. It is used to force vanishing of a Tate module on which Frobenius acts by a scalar, in [`ModularCurve.tateModule_eq_zero_of_forall_frobenius_smul_eq_mul_smul`](thm.html#ModularCurve.tateModule_eq_zero_of_forall_frobenius_smul_eq_mul_smul), and thence in the bound on Fourier coefficients of normalised eigenforms [`CuspForm.qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform`](thm.html#CuspForm.qCoeff_sq_ne_one_add_sq_of_isNormalizedEigenform).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JZero.exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] :
    ∃ B : TateModule p (ModularCurve.JZero M) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JZero M) →ₗ[ℤ_[p]]
        ℤ_[p],
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : TateModule p (ModularCurve.JZero M)),
        B (TateModule.rep p (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
            (TateModule.rep p (ModularCurve.JZero M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
              y) =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) * B x y) ∧
      (∀ x, (∀ y, B x y = 0) → x = 0) ∧
      (∀ y, (∀ x, B x y = 0) → y = 0) := by sorry
