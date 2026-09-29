-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
-- name    : ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/a53b1d0e-aa5e-5fd1-bb39-2ec07c80c725
-- title:
--   Points of H_m over 𝔽̄₂ number a power of two
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of `LiesOverPrime`, i.e. the image of $p$ in $\overline{\mathbb Q}$ is a non-unit of $A$. Let $C$ be a term of the structure `JZeroNeronPrimaryTorsionCore p 2 A hA`; its data consist of a family of abelian-group sheaves $\mathcal J_m$ on the small fppf site of $\mathrm{Spec}\,\mathbb Z$ together with a family of commutative rings $H_m$, each carrying a $\mathbb Z$-Hopf algebra structure and flat and of finite type over $\mathbb Z$, whose $\mathbb Z$-algebra homomorphisms into the sections of an fppf cover compute the sections of $\mathcal J_m$ functorially, together with: finiteness of $H_m$ after base change to $\mathbb Z$ localised away from $\ell$ for primes $\ell \neq p$; bijections, additive and Galois-equivariant, of the points of $H_m$ over $\overline{\mathbb Q}$ with the $2^m$-torsion of $J_0(p)$ annihilated by a power of the Eisenstein maximal ideal at $2$, and of its points over $A$ with the toric part thereof; sheaves $Q_m$ fitting into short exact sequences with $\mathcal J_m \to \mathcal J_{m+1}$; and a Kummer row datum; the remaining fields are summarised here. For every $m$, the conclusion asserts the existence of $a \in \mathbb N$ with $\#\,\mathrm{Hom}_{\mathbb Z\text{-alg}}(H_m, \overline{\mathbb F}_2) = 2^a$, where $\overline{\mathbb F}_2$ is `AlgebraicClosure (ZMod 2)`; since $2^a \neq 0$ and `Nat.card` vanishes on infinite types, this also asserts that the set of such homomorphisms is finite.
--
--   This is the point-count ingredient in Mazur's analysis of the $2$-primary Eisenstein torsion of $J_0(p)$: the finite flat group scheme over $\mathbb Z$ represented by $H_m$ has $2$-power order, as read off from its $\overline{\mathbb F}_2$-points. It is used in the inductive comparison of the orders at successive levels, [`ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_natCard_algHom_succ_eq_pow_mul_natCard_algHom_castSucc_two), and in [`ModularCurve.JZeroNeronPrimaryTorsionSheaf.prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionSheaf.prop17_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ) :
    ∃ a : ℕ, Nat.card (C.H m →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a := by sorry
