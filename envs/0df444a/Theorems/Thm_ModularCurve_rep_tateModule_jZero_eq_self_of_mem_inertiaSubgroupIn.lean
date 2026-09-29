-- Prove2me | Theorems.Thm_ModularCurve_rep_tateModule_jZero_eq_self_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.rep_tateModule_jZero_eq_self_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/cab0d2a7-80c3-52ce-8751-eea8f8ab5b16
-- title:
--   Inertia at ℓ ∤ Np acts trivially on Tₚ J₀(N)
-- statement:
--   Fix $N \ge 1$ and a prime $p$, and let $J_0(N)$ denote [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115), the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the modular function field of level $N$ base-changed to $\overline{\mathbb Q}$, carrying its natural action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q\text{-alg}} \overline{\mathbb Q}$. Assume [`ModularCurve.HeckeOperatorsCommuteBar N`](def/ModularCurve_HeckeModule.html#L25), i.e. that the operators `heckeOperatorBar N ℓ` for primes $\ell$ commute pairwise on $J_0(N)$. Let $\ell$ be a prime with $\ell \nmid Np$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $A.\mathrm{LiesOverPrime}\ \ell$, meaning that the image of $\ell$ lies in the nonunits of $A$, and let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ belonging to `A.inertiaSubgroupIn ℚ`, the image in the full automorphism group of the inertia subgroup of the decomposition subgroup at $A$. Finally let $x$ be an element of [`TateModule p (JZero N)`](def/EllipticCurve_TateModule.html#L15): a sequence $(x_n)_{n \in \mathbb N}$ in $J_0(N)$ with $p^n x_n = 0$ and $p\, x_{n+1} = x_n$ for all $n$. Then $\sigma$ acts as the identity on $x$ under [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174), which acts coordinatewise: $\sigma \cdot x_n = x_n$ for every $n$.
--
--   This is the Néron–Ogg–Shafarevich criterion for the modular Jacobian: the $p$-adic representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $T_p J_0(N)$ is unramified at every prime $\ell \nmid Np$. It supplies the unramifiedness input for the statements attaching $p$-adic Galois representations with prescribed Frobenius characteristic polynomials to Hecke characters and to normalized eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rep_tateModule_jZero_eq_self_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.rep_tateModule_jZero_eq_self_of_mem_inertiaSubgroupIn (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓNp : ¬ ℓ ∣ N * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : TateModule p (ModularCurve.JZero N)) :
    TateModule.rep p (ModularCurve.JZero N) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x = x := by sorry
