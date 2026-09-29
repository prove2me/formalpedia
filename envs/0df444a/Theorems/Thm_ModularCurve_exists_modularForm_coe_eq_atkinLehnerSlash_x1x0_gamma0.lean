-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_x1x0_gamma0
-- name    : ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_x1x0_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/ae40eba0-6cd6-552d-9b8d-a1bf0efbc3c2
-- title:
--   Atkin–Lehner operator preserves forms on Γ₁(M)∩Γ₀(p)
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number with $p \nmid M$, and let $k$ be an integer. Let $\Gamma$ denote the image in $\mathrm{GL}_2(\mathbb{R})$ of the subgroup $\Gamma_1(M) \cap \Gamma_0(p)$ of $\mathrm{SL}_2(\mathbb{Z})$, and let $f$ be a modular form of weight $k$ for $\Gamma$. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M)$ and satisfy $p \mid \gamma_{11}$, where $\gamma_{11}$ is the lower right entry. Then there exists a modular form $F$ of weight $k$ for the same group $\Gamma$ whose underlying function $\mathbb{H} \to \mathbb{C}$ is given by
--   $$F(\tau) = \bigl(f \mid_k \gamma\bigr)\bigl(\mathrm{diag}(p,1) \cdot \tau\bigr),$$
--   where $\mid_k$ is the weight-$k$ slash action on functions on the upper half-plane and $\mathrm{diag}(p,1)$ is the element [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) of $\mathrm{GL}_2(\mathbb{R})$, namely the upper triangular matrix $!![p,0;0,1]$ (for $p \neq 0$), acting on $\mathbb{H}$ by $\tau \mapsto p\tau$. The assertion is thus that the function $\tau \mapsto (f\mid_k\gamma)(p\tau)$ is holomorphic, of weight $k$ for $\Gamma$, and bounded at the cusps.
--
--   This is the statement that the Atkin–Lehner type operator attached to the matrix $W = \gamma\,\mathrm{diag}(p,1)$, with $\gamma \in \Gamma_0(M)$ having $p$-divisible lower right entry, carries weight-$k$ modular forms on $\Gamma_1(M) \cap \Gamma_0(p)$ to forms on the same group; the underlying point is that such $W$ normalises $\Gamma_1(M) \cap \Gamma_0(p)$. It feeds the analysis of Hecke and degeneracy operators at $p$ on forms of level $\Gamma_1(M) \cap \Gamma_0(p)$, and is cited by [`ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0`](thm.html#ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_x1x0_gamma0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_x1x0_gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm in

theorem ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_x1x0_gamma0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F : UpperHalfPlane → ℂ) = fun τ : UpperHalfPlane =>
        ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ) := by sorry
