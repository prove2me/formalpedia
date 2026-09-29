-- Prove2me | Theorems.Thm_ModularCurve_JH_exists_finiteFlat_prolongation_pi_torsion_diamondTwist_of_not_dvd_of_galoisFactorsThroughFiniteLevel
-- name    : ModularCurve.JH.exists_finiteFlat_prolongation_pi_torsion_diamondTwist_of_not_dvd_of_galoisFactorsThroughFiniteLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/4aacf5c4-c836-5cad-8761-af1b241dea70
-- title:
--   Finite flat model for twisted pⁿ-torsion of J_H(M)
-- statement:
--   Let $M\ge 1$, let $H\le(\mathbb Z/M)^\times$ be a subgroup, let $p$ be a prime with $p\nmid M$, and let $\delta\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to(\mathbb Z/M)^\times$ be a group homomorphism subject to two conditions: first, for every valuation subring $P$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$, every element of the inertia subgroup of $P$ over $\mathbb Q$ (the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup inside the decomposition subgroup) is sent to $1$; second, [`GaloisFactorsThroughFiniteLevel δ`](def/GaloisRep_Residual.html#L17), i.e. there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ such that every automorphism fixing $L$ pointwise is sent to $1$. Let $b,n\in\mathbb N$. Then there exist a type $G$ carrying a commutative ring structure and a Hopf algebra structure over the subring $\mathbb Z_{(p)}=\{q\in\mathbb Q : \gcd(\mathrm{den}(q),p)=1\}$ of $\mathbb Q$, such that $G$ is a finite flat $\mathbb Z_{(p)}$-module with cocommutative comultiplication, together with a bijection $e$ from the set of $\mathbb Z_{(p)}$-algebra homomorphisms $G\to\overline{\mathbb Q}$, equipped with its convolution monoid structure (`WithConv`), to $\mathrm{Fin}\,b\to J_H(M)[p^n]$, where $J_H(M)$ denotes the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the field [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123) over $\overline{\mathbb Q}$ — the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the level-$(M,H)$ function field inside $\mathbb Q((q))$ — and $J_H(M)[p^n]$ is the subgroup of elements killed by $p^n$, with the following two properties: $e$ is additive, $e(f\cdot g)=e(f)+e(g)$ for the convolution product; and for every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and all $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in G$, one has, for each index $i$, the identity $e(g)_i=\langle\delta(\sigma)\rangle\bigl(\sigma\cdot e(f)_i\bigr)$ in $J_H(M)$, where $\langle\,\cdot\,\rangle$ is [`ModularCurve.diamondHBar M H`](def/ModularCurve_XHOperators.html#L57), the additive endomorphism of $J_H(M)$ induced by the diamond automorphism of the function field over $\overline{\mathbb Q}$.
--
--   This is the good-reduction input at primes $p\nmid M$: the $p^n$-torsion of the $b$-fold product of the Jacobian $J_H(M)$, with the Galois action twisted by a diamond character $\delta$ that is unramified at $p$ and of finite level, is realised as the $\overline{\mathbb Q}$-points of a finite flat cocommutative Hopf algebra over $\mathbb Z_{(p)}$, that is, of a finite flat group scheme over $\mathbb Z_{(p)}$. It is used in the proof of [`CuspForm.TWLevel.HeckeRing.isFlatAt_of_not_dvd_level`](thm.html#CuspForm.TWLevel.HeckeRing.isFlatAt_of_not_dvd_level), where flatness of the relevant Galois representation at primes not dividing the level is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JH_exists_finiteFlat_prolongation_pi_torsion_diamondTwist_of_not_dvd_of_galoisFactorsThroughFiniteLevel.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JH.exists_finiteFlat_prolongation_pi_torsion_diamondTwist_of_not_dvd_of_galoisFactorsThroughFiniteLevel
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)

    (δ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod M)ˣ)
    (hδ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, δ σ = 1)

    (hδc : GaloisFactorsThroughFiniteLevel δ)
    (b n : ℕ) :
    ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
      Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
      ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
            (ModularCurve.xHFunctionFieldBar M H) (p ^ n))),
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : G, g h = σ (f h)) →
            ∀ i : Fin b, ((e g i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                (ModularCurve.xHFunctionFieldBar M H) (p ^ n))) : ModularCurve.JH M H) =
              ModularCurve.diamondHBar M H (δ σ)
                (σ • ((e f i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                  (ModularCurve.xHFunctionFieldBar M H) (p ^ n))) : ModularCurve.JH M H)) := by sorry
