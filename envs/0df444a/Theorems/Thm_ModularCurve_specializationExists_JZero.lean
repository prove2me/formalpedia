-- Prove2me | Theorems.Thm_ModularCurve_specializationExists_JZero
-- name    : ModularCurve.specializationExists_JZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/2354ec02-1bdf-5cc2-9ad1-5555656e9f6d
-- title:
--   Eichler–Shimura specialisation for J₀(N) at good primes
-- statement:
--   Fix a level $N \ge 1$ and a natural number $p$, and suppose [`ModularCurve.HeckeOperatorsCommuteBar N`](def/ModularCurve_HeckeModule.html#L25) holds, i.e. the operators $T_\ell =$ `heckeOperatorBar N ℓ` on $J =$ `JZero N` commute pairwise, so that the total module structure `heckeModuleBar N` used here is the action of $\mathbb{T} =$ `HeckeAlg` $= \mathbb{Z}[x_\ell : \ell \text{ prime}]$ in which the generator at $\ell$ acts by $T_\ell$. Here `JZero N` is the group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the modular function field of level $N$, that is, degree-zero divisor classes modulo principal divisors, with its $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$-action. Assuming further that the Galois action commutes with the $\mathbb{T}$-action, the conclusion is `SpecializationExists` for $K = \mathbb{Q}$, $L = \overline{\mathbb{Q}}$, the integers $N, p$ and the module $J$: for every prime $\ell$ with $\ell \nmid Np$ and every valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, there are an abelian group $J'$ with a $\mathbb{T}$-module structure, an additive map $\mathrm{sp} : J \to J'$ and an additive endomorphism $F$ of $J'$ such that $\mathrm{sp}$ is $\mathbb{T}$-equivariant, $\mathrm{sp}(\sigma \cdot x) = \mathrm{sp}(x)$ for all $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, $\mathrm{sp}(\sigma \cdot x) = F(\mathrm{sp}(x))$ for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ that is a Frobenius at $\ell$ for $A$, $\mathrm{sp}$ kills no nonzero element of $p$-power torsion, and $F^2 - T_\ell F + \ell = 0$ on $J'$.
--
--   This packages the Eichler–Shimura congruence relation $T_\ell = \mathrm{Frob}_\ell + \ell\,\mathrm{Ver}_\ell$ on the reduction of $J_0(N)$ at a prime $\ell \nmid Np$, together with injectivity of reduction on $p$-power torsion, in the shape consumed by the abstract specialisation layer of the argument. It is the input used to show that the $p$-power torsion of $J_0(N)$ is unramified outside $Np$ and satisfies the quadratic Frobenius relation, and hence feeds the construction of the residual Galois representations attached to modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_specializationExists_JZero.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.specializationExists_JZero (N p : ℕ) [NeZero N] (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) : letI := ModularCurve.heckeModuleBar N; ∀ (_ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg (ModularCurve.JZero N)), ModularCurve.SpecializationExists (K := ℚ) (L := AlgebraicClosure ℚ) N p (ModularCurve.JZero N) := by sorry
