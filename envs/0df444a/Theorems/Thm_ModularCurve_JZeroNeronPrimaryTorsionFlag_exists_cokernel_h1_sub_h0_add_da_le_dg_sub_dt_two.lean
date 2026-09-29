-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_h1_sub_h0_add_da_le_dg_sub_dt_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_da_le_dg_sub_dt_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/be4f5507-2e2a-5889-93d1-031d3af4f16c
-- title:
--   Per-layer cohomology inequality l₁-l₀+dₐ≤ d_g-dₜ at 2
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ lying in the nonunits of $A$ (the hypothesis `LiesOverPrime`), a datum $C$ of type `JZeroNeronPrimaryTorsionCore p 2 A hA` — the package of fppf sheaves $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$ together with flat finite-type Hopf $\mathbb Z$-algebras representing them, their generic and $A$-integral point identifications with the $2$-primary Eisenstein torsion of $J_0(p)$, and the associated Kummer rows — a natural number $m$, and a flag `flag` of type `JZeroNeronPrimaryTorsionFlag p 2 A hA C m`, that is a filtration $F_0\subseteq\cdots\subseteq F_{n}$ of the $2^m$-torsion sheaf with inclusions `incl`, a compatible tower of Hopf algebras $G_i$ with surjections, and an increasing family of Galois-stable subgroups `genericStep` of $J_0(p)(\overline{\mathbb Q})$ inside $\bar{\mathfrak e}$-primary torsion, from $\bot$ to the full group. Let $i$ be an index of the flag, $L$ an abelian sheaf on that site, and $pr : F_{i+1}\to L$ a morphism with $\mathrm{incl}_i$ followed by $pr$ zero, such that the resulting short complex is short exact, so that $L$ realises the $i$-th graded piece. Let $d_g,d_t,d_a$ be natural numbers such that the order of $\mathrm{genericStep}(i+1)$ is $2^{d_g}$ times that of $\mathrm{genericStep}(i)$; the order of the intersection of $\mathrm{genericStep}(i+1)$ with `jZeroToricTorsion p A (2 ^ m)` — the $2^m$-torsion of $J_0(p)$ intersected with the image of the inertia-invariant points under multiplication by the Eisenstein numerator — is $2^{d_t}$ times the same intersection for $\mathrm{genericStep}(i)$; and the number of $\mathbb Z$-algebra homomorphisms $G_{i+1}\to\overline{\mathbb F}_2$ is $2^{d_a}$ times the number for $G_{i}$. Then there exist $l_0,l_1\in\mathbb N$ with $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, L)=2^{l_0}$, $\#H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, L)=2^{l_1}$ and $l_1-l_0+d_a\le d_g-d_t$ as integers.
--
--   This is the layer-by-layer form, at the prime $2$, of the numerical inequality underlying Mazur's Proposition I.1.7 on the Eisenstein ideal, expressed in the invariants $\delta$ and $\alpha$: each graded piece of the flag has finite $2$-group cohomology on the fppf site of $\operatorname{Spec}\mathbb Z$, and the defect $l_1-l_0+d_a$ is bounded by the difference of the generic and toric step exponents. Summing it over the layers of the flag gives the global inequality $h^1+a\le h^0+\delta$ used in [`ModularCurve.JZeroNeronPrimaryTorsionSheaf.h1_add_le_h0_add_delta_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionSheaf.h1_add_le_h0_add_delta_of_forall_nonempty_jZeroNeronPrimaryTorsionFlag_two); the proof here combines the sharper per-layer bound `exists_cokernel_dt_le_h0_and_h1_add_da_le_one_two` with the Hopf-algebra rank models of [`HopfAlgebra.exists_constant_and_rootsOfUnity_models_of_rank`](thm.html#HopfAlgebra.exists_constant_and_rootsOfUnity_models_of_rank).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_h1_sub_h0_add_da_le_dg_sub_dt_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_da_le_dg_sub_dt_two
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p 2 A hA C m) (i : Fin flag.n)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact)
    (dg dt da : ℕ)
    (hg : Nat.card ↥(flag.genericStep i.succ) = 2 ^ dg * Nat.card ↥(flag.genericStep i.castSucc))
    (ht : Nat.card ↥(jZeroToricTorsion p A (2 ^ m) ⊓ flag.genericStep i.succ)
        = 2 ^ dt * Nat.card ↥(jZeroToricTorsion p A (2 ^ m) ⊓ flag.genericStep i.castSucc))
    (ha : Nat.card (flag.G i.succ →ₐ[ℤ] AlgebraicClosure (ZMod 2))
        = 2 ^ da * Nat.card (flag.G i.castSucc →ₐ[ℤ] AlgebraicClosure (ZMod 2))) :
    ∃ l0 l1 : ℕ,
      Nat.card (fppfCohomology specInt L 0) = 2 ^ l0 ∧
      Nat.card (fppfCohomology specInt L 1) = 2 ^ l1 ∧
      (l1 : ℤ) - l0 + da ≤ (dg : ℤ) - dt := by sorry
