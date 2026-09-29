-- Prove2me | Theorems.Thm_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one
-- name    : ModularForm.exists_cuspForm_coeffHeckeT_eq_of_modEq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/46844fb3-8f60-59ba-839b-d4dd15fd31b7
-- title:
--   T_ℓ acts as 1+ℓ^{k-1} modulo cusp forms
-- statement:
--   Let $N'$ be a natural number, assumed nonzero, let $k$ be an integer, and let $f$ be a modular form of weight $k$ for the congruence subgroup $\Gamma_0(N')$. Let $\ell$ be a prime number with $\ell \equiv 1 \pmod{N'}$. Then there is a cusp form $g$ of weight $k$ for $\Gamma_0(N')$ such that for every natural number $n$ the identity
--   $$a_{n\ell}(f) + \begin{cases} \ell^{k-1}\, a_{n/\ell}(f) & \ell \mid n\\ 0 & \text{otherwise}\end{cases} \;=\; (1 + \ell^{k-1})\, a_n(f) + a_n(g)$$
--   holds in $\mathbb{C}$, where for a function $h$ on the upper half-plane $a_n(h)$ denotes the $n$-th coefficient of its $q$-expansion of width $1$, i.e. in the variable $q = e^{2\pi i \tau}$, and $\ell^{k-1}$ is the complex power (a negative power of $\ell$ when $k \le 0$). The left-hand side is exactly the $n$-th coefficient of the purely coefficient-level Hecke operator [`ModularForm.coeffHeckeT`](def/ModularForm_HeckeOperator.html#L162) of weight $k$ and index $\ell$ applied to the coefficient sequence of $f$; no claim is made here that this sequence is itself the $q$-expansion of a modular form.
--
--   This is the Eisenstein half of the Eisenstein/cuspidal dichotomy in characteristic zero: at a prime $\ell \equiv 1 \pmod{N'}$ every Eisenstein constituent of $M_k(\Gamma_0(N'))$ has $T_\ell$-eigenvalue $1 + \ell^{k-1}$, so $T_\ell - (1+\ell^{k-1})$ carries $M_k(\Gamma_0(N'))$ into $S_k(\Gamma_0(N'))$. It is used in the analysis of mod $p$ eigenforms attached to a Weierstrass curve, where it separates cuspidal from Eisenstein behaviour in the irreducible-residual-representation case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_cuspForm_coeffHeckeT_eq_of_modEq_one.lean

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularForm.exists_cuspForm_coeffHeckeT_eq_of_modEq_one
    (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N']) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N') k, ∀ n : ℕ,
      ModularForm.coeffHeckeT k ℓ (ModularFormClass.qCoeff f) n =
        (1 + (ℓ : ℂ) ^ (k - 1)) * ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by sorry
