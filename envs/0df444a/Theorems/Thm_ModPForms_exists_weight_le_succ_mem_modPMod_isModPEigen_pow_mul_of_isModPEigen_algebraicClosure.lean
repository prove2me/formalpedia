-- Prove2me | Theorems.Thm_ModPForms_exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure
-- name    : ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/a6c421ad-8b04-59b9-958e-0e00818b85dd
-- title:
--   Mod p eigensystems occur, up to twist, in weight ≤ p+1
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $N'$ be a nonzero natural number with $p \nmid N'$, let $S_0$ be a finite set of natural numbers with $p \in S_0$, and write $F =$ `AlgebraicClosure (ZMod p)`. Let $k$ be an integer with $k \ge 2$, let $\varphi \in F[[q]]$ and let $\mathrm{lam} : \mathbb{N} \to F$. Assume $\varphi$ lies in `modPMod N' k F`, the $F$-span inside $F[[q]]$ of the power series of the form $\sum_n \bar{a}_n q^n$ where $a : \mathbb{N} \to \mathbb{Z}$ is an integral sequence realising the $q$-expansion coefficients (`qCoeff`, the coefficients of the width-one $q$-expansion) of some modular form of weight $k$ on $\Gamma_0(N')$, reduced into $F$. Assume further `IsModPEigen N' S₀ k φ lam`: $\varphi \ne 0$ and, for every prime $\ell$ with $\ell \nmid N'$ and $\ell \notin S_0$, one has `heckePS k ℓ φ` $= \mathrm{lam}(\ell)\,\varphi$, where `heckePS k ℓ` is the operator on power series sending $\varphi$ to the series with $n$-th coefficient $c_{n\ell}(\varphi) + \ell^{\,k-1} c_{n/\ell}(\varphi)$ when $\ell \mid n$, and $c_{n\ell}(\varphi)$ otherwise. Then there exist an integer $k'$ with $2 \le k' \le p+1$, a natural number $j$, a power series $\psi \in$ `modPMod N' k' F` and $\mathrm{mu} : \mathbb{N} \to F$ such that $\psi$ is nonzero and is an eigenvector of the same operators in weight $k'$ with eigenvalues $\mathrm{mu}(\ell)$, and $\mathrm{mu}(\ell) = \ell^{\,j}\,\mathrm{lam}(\ell)$ (with $\ell$ taken in $F$) for every prime $\ell$ with $\ell \nmid N'$ and $\ell \notin S_0$.
--
--   This is the weight-window statement for systems of mod $p$ Hecke eigenvalues, in the form given by Edixhoven's theta-cycle analysis: any eigensystem of level prime to $p$ occurring in some weight $\ge 2$ also occurs, after twisting the eigenvalues by a power of $\ell$, in a weight between $2$ and $p+1$. It is stated here over the single coefficient field $\overline{\mathbb{F}}_p$, which is the field at which the weight bound for the residual representation attached to a Frey curve is read off, and it is used by [`WeierstrassCurve.exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two`](thm.html#WeierstrassCurve.exists_ideal_heckeAlgebra_weight_le_succ_pow_mul_of_pow_mul_of_exists_prime_dvd_mod_three_eq_two); the proof invokes [`ModPForms.nonempty_ssDatum_algebraicClosure`](thm.html#ModPForms.nonempty_ssDatum_algebraicClosure) for the existence of the supersingular data attached to $p$, $N'$ and $S_0$ over $\overline{\mathbb{F}}_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure.lean

import Definitions.Def_CuspForm_ModPForms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries (AlgebraicClosure (ZMod p))) (lam : ℕ → AlgebraicClosure (ZMod p))
    (hφ : φ ∈ modPMod N' k (AlgebraicClosure (ZMod p))) (heig : IsModPEigen N' S₀ k φ lam) :
    ∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧ ∃ (j : ℕ) (ψ : PowerSeries (AlgebraicClosure (ZMod p))) (mu : ℕ → AlgebraicClosure (ZMod p)),
      ψ ∈ modPMod N' k' (AlgebraicClosure (ZMod p)) ∧ IsModPEigen N' S₀ k' ψ mu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → mu ℓ = (ℓ : AlgebraicClosure (ZMod p)) ^ j * lam ℓ := by sorry
