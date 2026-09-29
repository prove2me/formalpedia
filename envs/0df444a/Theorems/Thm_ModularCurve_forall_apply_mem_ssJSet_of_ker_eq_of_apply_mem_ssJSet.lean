-- Prove2me | Theorems.Thm_ModularCurve_forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet
-- name    : ModularCurve.forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/442bca55-d90f-51b1-b3c8-cf292ea9f0a4
-- title:
--   Supersingularity of a depends only on kerφ
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring in a universe $u$, and let $a \in R$. Let $\Omega_0$ be a field in the same universe $u$, of characteristic $p$ and algebraically closed, and let $\varphi_0 \colon R \to \Omega_0$ be a ring homomorphism such that $\varphi_0(a)$ lies in `ssJSet p Ω₀`, i.e. for every Weierstrass curve $W$ over $\Omega_0$ which is elliptic and satisfies $j(W) = \varphi_0(a)$, every point $P$ of the associated affine curve with $p \cdot P = 0$ is the zero point. The assertion is then: for every field $\Omega$ in `Type` (the smallest universe) which is of characteristic $p$ and algebraically closed, and every ring homomorphism $\varphi \colon R \to \Omega$ with $\ker \varphi = \ker \varphi_0$ as ideals of $R$, the element $\varphi(a)$ lies in `ssJSet p Ω`, that is, no elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(a)$ has a nonzero point killed by $p$. Thus membership of the image of $a$ in the set of $p$-torsion-free $j$-invariants over an algebraically closed field of characteristic $p$ depends only on the kernel of the homomorphism, not on the homomorphism or on the target field.
--
--   Over an algebraically closed field of characteristic $p$ the set `ssJSet p Ω` is the set of supersingular $j$-invariants, so the statement says that supersingularity of the reduction of $a$ at the prime ideal $\ker \varphi_0$ is decided by any single geometric point of $\operatorname{Spec} R$ with that kernel. It is used when supersingularity conditions obtained from one chosen geometric fibre must be transported to other fibres, in the study of integral models of modular curves and of the maximal ideals of their coordinate rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

universe u

theorem ModularCurve.forall_apply_mem_ssJSet_of_ker_eq_of_apply_mem_ssJSet
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (a : R)
    {Ω₀ : Type u} [Field Ω₀] [CharP Ω₀ p] [IsAlgClosed Ω₀] [DecidableEq Ω₀]
    (φ₀ : R →+* Ω₀) (h₀ : φ₀ a ∈ ssJSet p Ω₀) :
    ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ : R →+* Ω),
      RingHom.ker φ = RingHom.ker φ₀ → φ a ∈ ssJSet p Ω := by sorry
