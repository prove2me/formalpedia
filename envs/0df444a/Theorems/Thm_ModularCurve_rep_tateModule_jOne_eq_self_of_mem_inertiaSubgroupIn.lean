-- Prove2me | Theorems.Thm_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/ce512782-ba98-5828-9db0-58b8b5a3ceee
-- title:
--   Inertia away from Mp acts trivially on Tₚ J₁(M)
-- statement:
--   Fix a natural number $M \neq 0$ and a prime $p$, and let $\ell$ be a prime with $\ell \nmid M p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $\ell$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, and let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ belonging to `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup of $A$. Write $J =$ [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186) for the degree-zero divisor class group `Pic0` of the Laurent base change to $\overline{\mathbb{Q}}$ of the function field of $X_1(M)$, with its coefficientwise action of $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$. Let $x$ be an element of [`TateModule p J`](def/EllipticCurve_TateModule.html#L15), that is, a sequence $(x_n)_{n \in \mathbb{N}}$ of elements of $J$ with $p^n x_n = 0$ and $p\, x_{n+1} = x_n$ for all $n$. Then the $\mathbb{Z}_p$-linear endomorphism [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) attached to $\sigma$ fixes $x$: $\sigma$ acts as the identity on the $p$-adic Tate module of $J$.
--
--   This is the unramifiedness statement coming from good reduction of $J_1(M)$ at primes $\ell \nmid M$ together with the criterion of Néron–Ogg–Shafarevich: for $p \neq \ell$ the inertia group at a place above $\ell$ acts trivially on $T_p J_1(M)$. It is used in the construction of the $p$-adic Galois representations attached to eigenforms with nebentypus, where it supplies the unramifiedness outside $Mp$ needed for the Frobenius characteristic-polynomial relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.rep_tateModule_jOne_eq_self_of_mem_inertiaSubgroupIn (M p : ℕ) [NeZero M]
    [Fact p.Prime]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : TateModule p (ModularCurve.JOne M)) :
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x = x := by sorry
