-- Prove2me | Theorems.Thm_ModularCurve_ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
-- name    : ModularCurve.ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/0c8237df-de4c-550e-9c6b-4ecd9d291a9e
-- title:
--   Inertia at p ∥ M commutes with a Fricke-type automorphism
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number, and let $H$ be a subgroup of $(\mathbb Z/M)^{\times}$. Assume $p \mid M$ but $p^{2} \nmid M$, and that $H$ contains every unit of $\mathbb Z/M$ whose image under the reduction map $(\mathbb Z/M)^{\times} \to (\mathbb Z/(M/p))^{\times}$ is $1$. Let $Pl$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense that $p$ is a nonunit of $Pl$. Let $w$ be an $\overline{\mathbb Q}$-algebra automorphism of [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123), the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the rational function field `xHFunctionField M H`; it acts on [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127), the degree-zero divisor classes (degree-zero divisors modulo principal ones) of that field, through its image $(w,1)$ in the group of semilinear automorphisms, [`AlgebraicCurve.SemilinearAut.ofAlgAut w`](def/AlgebraicCurve_BaseChangeGalois.html#L76). Assume the twisting law `hw4`: for every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and every $c$ coprime to $M$ with $\sigma\zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{M}=1$, one has $w_{*}(\sigma \cdot x) = \sigma \cdot \langle c\rangle_{*}(w_{*}x)$ for all $x$, where $\langle c \rangle_{*}$ is [`ModularCurve.diamondHBar M H`](def/ModularCurve_XHOperators.html#L57) at the unit determined by $c$. Then for every $\sigma$ in the inertia subgroup of $Pl$ over $\mathbb Q$ (the image in $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ of the inertia subgroup inside the decomposition subgroup) and every $x \in$ `JH M H`, one has $w_{*}(\sigma \cdot x) = \sigma \cdot w_{*}x$.
--
--   This is the statement that a Fricke/Atkin–Lehner type automorphism of the Jacobian of $X_H(M)$, which in general is only defined up to a diamond twist by the mod-$M$ cyclotomic character, commutes with inertia at a prime $p$ exactly dividing $M$ once $H$ contains the kernel of reduction to level $M/p$. It is used in the analysis of the Néron model of $J_H(M)$ at $p$, where the induced involution must be seen to preserve the toric and cyclotomic-inertia parts of the component structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ofAlgAut_smul_galois_smul_eq_of_mem_inertiaSubgroupIn_of_frickeGaloisTwist
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] ModularCurve.xHFunctionFieldBar M H)

    (hw4 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ModularCurve.JH M H,
          AlgebraicCurve.SemilinearAut.ofAlgAut w • (σ • x)
            = σ • ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (AlgebraicCurve.SemilinearAut.ofAlgAut w • x))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ Pl.inertiaSubgroupIn ℚ) (x : ModularCurve.JH M H) :
    AlgebraicCurve.SemilinearAut.ofAlgAut w • (σ • x) = σ • (AlgebraicCurve.SemilinearAut.ofAlgAut w • x) := by sorry
