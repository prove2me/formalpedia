-- Prove2me | Theorems.Thm_ModularCurve_exists_bilinForm_tateModule_nondegenerate_hecke_galois
-- name    : ModularCurve.exists_bilinForm_tateModule_nondegenerate_hecke_galois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/a0cbc5cc-3ff7-59dd-9ac6-f0fde8824bef
-- title:
--   Hecke-self-adjoint Galois pairing on the Tate module of J₀(p)
-- statement:
--   Let $p$ and $\ell$ be primes. Write $J_0(p)$ for `JZero p`, the degree-zero divisor classes modulo principal divisors of the level-$p$ modular function field base-changed to $\overline{\mathbf Q}$, equipped with the module structure `heckeModuleBar p` over $\mathbb{T} =$ `HeckeAlg` $= \mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbf Z$ (the polynomial variables act by the operators `heckeOperatorBar` when these commute with one another, and by $0$ otherwise), and write $T_\ell J_0(p)$ for [`TateModule ℓ (JZero p)`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)_{n \ge 0}$ in $J_0(p)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$, a $\mathbf Z_\ell$-module. Then there exists a $\mathbf Z_\ell$-bilinear form $B_f \colon T_\ell J_0(p) \times T_\ell J_0(p) \to \mathbf Z_\ell$ such that: $B_f(x,\cdot) = 0$ forces $x = 0$ and $B_f(\cdot,y) = 0$ forces $y = 0$; $B_f(tx,y) = B_f(x,ty)$ for every $t \in \mathbb{T}$, acting componentwise through `tateHeckeRep`; and, for every $\mathbf Q$-algebra automorphism $\sigma$ of $\overline{\mathbf Q}$, every $k$ and every natural number $n_k$ with $\sigma\zeta = \zeta^{n_k}$ for all $\zeta \in \overline{\mathbf Q}$ satisfying $\zeta^{\ell^k} = 1$, one has $B_f(\sigma x, \sigma y) - n_k B_f(x,y) \in \ell^k \mathbf Z_\ell$, where $\sigma$ acts componentwise on the Tate module via [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174).
--
--   This is the $\ell$-adic Weil pairing on the Tate module of the Jacobian of $X_0(p)$, twisted so that the Hecke operators become self-adjoint rather than adjoint to their Rosati duals, with the Galois transformation law recorded in the weakened levelwise form of a congruence modulo $\ell^k$ against the cyclotomic character. It is obtained from the levelwise pairings of [`ModularCurve.exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat`](thm.html#ModularCurve.exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat) together with the lifting statement [`ModularCurve.exists_tateModule_apply_eq_of_pow_smul_eq_zero`](thm.html#ModularCurve.exists_tateModule_apply_eq_of_pow_smul_eq_zero), and is used in the analysis of inertia on the Tate module in [`ModularCurve.exists_generator_tateModule_closure_inertia_smul_sub_adjoin_tateHeckeRep`](thm.html#ModularCurve.exists_generator_tateModule_closure_inertia_smul_sub_adjoin_tateHeckeRep).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bilinForm_tateModule_nondegenerate_hecke_galois.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_JZeroTateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_bilinForm_tateModule_nondegenerate_hecke_galois
    (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] :
    letI := heckeModuleBar p
    ∃ Bf : TateModule ℓ (JZero p) →ₗ[ℤ_[ℓ]] TateModule ℓ (JZero p) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],
      (∀ x, (∀ y, Bf x y = 0) → x = 0) ∧ (∀ y, (∀ x, Bf x y = 0) → y = 0) ∧
      (∀ (t : HeckeAlg) (x y : TateModule ℓ (JZero p)),
        Bf (tateHeckeRep ℓ (JZero p) t x) y = Bf x (tateHeckeRep ℓ (JZero p) t y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k nk : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ (ℓ ^ k) = 1 → σ ζ = ζ ^ nk) →
        ∀ x y : TateModule ℓ (JZero p),
          Bf (TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
              (TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y)
            - (nk : ℤ_[ℓ]) * Bf x y ∈ Ideal.span {((ℓ : ℤ_[ℓ]) ^ k)}) := by sorry
