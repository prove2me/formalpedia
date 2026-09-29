-- Prove2me | Theorems.Thm_ModularCurve_finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd
-- name    : ModularCurve.finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/823a6b53-94ea-5348-afa3-11dc6396c23b
-- title:
--   Finiteness of the kernel of T_ℓ-(ℓ+1) on J₀(N)
-- statement:
--   Let $N$ be a nonzero natural number and let $\ell$ be a prime not dividing $N$. Write $J_0(N)(\overline{\mathbf Q})$ for `JZero N`, the group `Pic0` of degree-zero divisors of the function field `modularFunctionFieldBar N` (the base change to $\overline{\mathbf Q}$ of the full modular function field of level $N$ inside Laurent series) over $\overline{\mathbf Q}$, modulo the subgroup of principal divisors. The Hecke algebra is taken to be the polynomial ring `HeckeAlg` $= \mathbf Z[X_r : r \text{ prime}]$ on indeterminates indexed by the primes, with `heckeGen ℓ` $= X_\ell$, and it acts on $J_0(N)(\overline{\mathbf Q})$ through the module structure `heckeModuleBar N`: if the operators `heckeOperatorBar N ℓ'` commute pairwise, the action is by the ring homomorphism sending $X_{\ell'}$ to `heckeOperatorBar N ℓ'`; otherwise it is by the evaluation homomorphism sending every indeterminate to $0$. The assertion is that the set of $x \in J_0(N)(\overline{\mathbf Q})$ annihilated by $X_\ell - (\ell+1)$, i.e. with $(X_\ell - C(\ell+1))\cdot x = 0$, is finite. (In the degenerate branch of the definition the element acts as multiplication by $-(\ell+1)$, whose kernel is the $(\ell+1)$-torsion.)
--
--   Classically this says that $\eta_\ell = T_\ell - (\ell+1)$ is an isogeny of $J_0(N)$ onto itself for $\ell \nmid N$, the finiteness being a consequence of the bound $|a_\ell| < \ell+1$ for eigenvalues of $T_\ell$ on weight-two cusp forms of level $N$ together with finiteness of torsion subgroups. It is used in the analysis of level data for the Eichler–Shimura relations, being cited by [`ModularCurve.SSLevelDatum.eq_empty_or_eq_univ_of_forall_fst_mem_iff_snd_mem`](thm.html#ModularCurve.SSLevelDatum.eq_empty_or_eq_univ_of_forall_fst_mem_iff_snd_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd
    (N : ℕ) [NeZero N] (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N) :
    letI := heckeModuleBar N
    {x : JZero N | (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x = 0}.Finite := by sorry
