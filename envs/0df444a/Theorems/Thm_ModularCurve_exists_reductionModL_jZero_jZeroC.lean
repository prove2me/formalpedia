-- Prove2me | Theorems.Thm_ModularCurve_exists_reductionModL_jZero_jZeroC
-- name    : ModularCurve.exists_reductionModL_jZero_jZeroC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/9da02bc0-e91e-5998-86e5-cdf6c1728b24
-- title:
--   Reduction of J₀(N) modulo ℓ∤ N
-- statement:
--   Let $N\ge 1$, let $\ell$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $\ell$ in the sense that $\ell$ is a non-unit of $A$, with residue field $k_A=$ `IsLocalRing.ResidueField A` of characteristic $\ell$. Write $J=$ [`ModularCurve.JZero N`](def/ModularCurve_ArithmeticGalois.html#L115) for the group of degree-zero divisor classes of the function field `modularFunctionFieldBar N` over $\overline{\mathbb Q}$, carrying its action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and $\bar J=$ [`ModularCurve.JZeroC k_A N`](def/ModularCurve_X0ModL.html#L148) for the degree-zero divisor class group of `modularFunctionFieldFullC k_A N` over $k_A$. The assertion is that there exists an additive homomorphism $\mathrm{red}\colon J\to\bar J$ such that: (i) $\mathrm{red}(\tau\cdot z)=\mathrm{red}(z)$ for every $\tau$ in `A.inertiaSubgroupIn ℚ`, the image in $\overline{\mathbb Q}$-automorphisms of the inertia subgroup of $A$, and every $z\in J$; (ii) for every $\sigma\in\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ lying in the decomposition subgroup of $A$ and inducing $x\mapsto x^{\ell}$ on $k_A$, one has $\mathrm{red}(\sigma\cdot z)=$ `frobeniusPushforwardModL k_A N ℓ` $(\mathrm{red}\,z)$ for all $z$; (iii) $\mathrm{red}$ intertwines `heckeOperatorBar N ⟨ℓ, _⟩` on $J$ with `heckeOperatorModL k_A N ℓ`, the sum of the Frobenius pushforward and pullback maps, on $\bar J$; and (iv) for every natural number $m$ with $\ell\nmid m$, any $z\in J$ with $mz=0$ and $\mathrm{red}(z)=0$ is zero.
--
--   This packages the good reduction of $J_0(N)$ at a prime $\ell$ not dividing the level, together with the Eichler–Shimura congruence relation $T_\ell\equiv\mathrm{Fr}_*+\mathrm{Fr}^*$ on the reduction and the injectivity of reduction on prime-to-$\ell$ torsion. It is used in the study of the specialisation kernel on $J_0(N)$, via [`ModularCurve.eq_zero_of_torsion_of_mem_specializationKernel_jZero`](thm.html#ModularCurve.eq_zero_of_torsion_of_mem_specializationKernel_jZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_reductionModL_jZero_jZeroC.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeOperatorModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_reductionModL_jZero_jZeroC (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ] :
    ∃ red : ModularCurve.JZero N →+ ModularCurve.JZeroC (IsLocalRing.ResidueField A) N,
      (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ z : ModularCurve.JZero N, red (τ • z) = red z) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        ∀ z : ModularCurve.JZero N,
          red (σ • z) = ModularCurve.frobeniusPushforwardModL (IsLocalRing.ResidueField A) N ℓ (red z)) ∧
      (∀ z : ModularCurve.JZero N,
        red (ModularCurve.heckeOperatorBar N ⟨ℓ, Fact.out⟩ z) =
          ModularCurve.heckeOperatorModL (IsLocalRing.ResidueField A) N ℓ (red z)) ∧
      (∀ m : ℕ, ¬ ℓ ∣ m → ∀ z : ModularCurve.JZero N, m • z = 0 → red z = 0 → z = 0) := by sorry
