-- Prove2me | Theorems.Thm_ModularCurve_exists_sub_C_mem_eisensteinIdeal
-- name    : ModularCurve.exists_sub_C_mem_eisensteinIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/8031df72-70e0-58b4-8d6a-7fa944405168
-- title:
--   T = ℤ + I_{Eis} at every level
-- statement:
--   Here `HeckeAlg` is the abstract Hecke algebra realised as the polynomial ring $\mathbb{Z}[T_\ell : \ell \text{ prime}]$, i.e. `MvPolynomial Nat.Primes ℤ`, with one indeterminate for each rational prime. For a natural number $N$, the Eisenstein system of level $N$ is the family of integers $a_\ell = 1$ when $\ell \mid N$ and $a_\ell = 1 + \ell$ when $\ell \nmid N$, and the Eisenstein ideal `eisensteinIdeal N` is by definition the `eigenIdeal` of this family, namely the kernel of the $\mathbb{Z}$-algebra homomorphism $\mathbb{Z}[T_\ell] \to \mathbb{Z}$ sending $T_\ell \mapsto a_\ell$ (evaluation of a polynomial at the Eisenstein system). The assertion is: for every $N : \mathbb{N}$ and every element $t$ of `HeckeAlg` there exists an integer $n$ such that $t - n$, with $n$ regarded as a constant polynomial via `MvPolynomial.C`, lies in `eisensteinIdeal N`. Equivalently, every element of the abstract Hecke algebra is congruent modulo the Eisenstein ideal of level $N$ to a rational integer. No hypotheses are imposed on $N$; in particular $N = 0$ is allowed, in which case every prime divides $N$ and the system is constantly $1$.
--
--   This is the elementary half of the statement that the quotient of the Hecke algebra by the Eisenstein ideal is a cyclic ring, i.e. $\mathbb{T} = \mathbb{Z} + I_{\mathrm{Eis}}$, in the shape needed later: it is used to produce integral characters and congruences modulo the Eisenstein ideal, and is cited by [`CuspForm.exists_ringHom_zmod_of_eisenstein_injective`](thm.html#CuspForm.exists_ringHom_zmod_of_eisenstein_injective) and by [`ModularCurve.exists_mem_eisensteinIdeal_heckeProj_eq_eisensteinNumerator`](thm.html#ModularCurve.exists_mem_eisensteinIdeal_heckeProj_eq_eisensteinNumerator).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sub_C_mem_eisensteinIdeal.lean

import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_sub_C_mem_eisensteinIdeal (N : ℕ) (t : HeckeAlg) : ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N := by sorry
