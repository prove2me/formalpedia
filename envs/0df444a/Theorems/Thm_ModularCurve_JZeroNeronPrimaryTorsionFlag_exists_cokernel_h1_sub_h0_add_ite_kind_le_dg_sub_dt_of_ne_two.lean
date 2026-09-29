-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_h1_sub_h0_add_ite_kind_le_dg_sub_dt_of_ne_two
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_ite_kind_le_dg_sub_dt_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/e9ef6d9a-a1f8-5efc-b985-bc9daa2cd1aa
-- title:
--   Layer inequality l₁-l₀+[const]≤ d_g-dₜ for odd q
-- statement:
--   Fix primes $p$ and $q$ with $q \neq 2$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ (the predicate `LiesOverPrime`), a localised Néron core $C$ of type `JZeroNeronPrimaryTorsionCore p q A hA`, a natural number $m$, and a flag `flag` of type `JZeroNeronPrimaryTorsionFlag p q A hA C m`, that is, a chain of fppf sheaves $\mathcal F_0, \dots, \mathcal F_n$ on $\operatorname{Spec}\mathbb Z$ with Hopf-algebra models, inclusions into $C.\mathcal J_m$, and an associated increasing chain `genericStep` of Galois-stable subgroups of $\mathrm{JZero}\,p = \mathrm{Pic}^0$ of the modular function field, rising from $\bot$ to `eisensteinPrimaryTorsionBar p q m`. Let $i$ be an index $< n$, let $L$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb Z$, and let $\mathrm{pr} : \mathcal F_{i+1} \to L$ be a morphism whose composite with the inclusion $\mathcal F_i \to \mathcal F_{i+1}$ vanishes and such that the resulting short complex $\mathcal F_i \to \mathcal F_{i+1} \to L$ is short exact. Assume natural numbers $d_g, d_t$ with $\#\,\mathrm{genericStep}(i+1) = q^{d_g}\cdot\#\,\mathrm{genericStep}(i)$ and $\#\bigl(\mathrm{jZeroToricTorsion}\,p\,A\,(q^m) \sqcap \mathrm{genericStep}(i+1)\bigr) = q^{d_t}\cdot\#\bigl(\mathrm{jZeroToricTorsion}\,p\,A\,(q^m) \sqcap \mathrm{genericStep}(i)\bigr)$, where $\mathrm{jZeroToricTorsion}\,p\,A\,(q^m)$ is the $q^m$-torsion of $\mathrm{JZero}\,p$ intersected with the image of the inertia-invariant points under multiplication by `eisensteinNumerator p`. Then there are natural numbers $l_0, l_1$ with $\#H^0_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, L) = q^{l_0}$, $\#H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, L) = q^{l_1}$ and, as integers, $l_1 - l_0 + \varepsilon \le d_g - d_t$, where $\varepsilon = 1$ if the flag's layer label `flag.kind i` is `const` and $\varepsilon = 0$ otherwise.
--
--   This is the layer-by-layer form of Mazur's Eisenstein-ideal cohomology count, in the localised setting where the flag lives on the $\mathfrak P$-primary Néron core attached to the place $A$: constant layers gain an extra unit over the toric count, multiplicative layers do not. It merges the two kind-specific estimates into a single uniform inequality and is used by [`ModularCurve.jZeroNeronTorsionSheaf_device_v5`](thm.html#ModularCurve.jZeroNeronTorsionSheaf_device_v5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_cokernel_h1_sub_h0_add_ite_kind_le_dg_sub_dt_of_ne_two.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_cokernel_h1_sub_h0_add_ite_kind_le_dg_sub_dt_of_ne_two
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact)
    (dg dt : ℕ)
    (hg : Nat.card ↥(flag.genericStep i.succ) = q ^ dg * Nat.card ↥(flag.genericStep i.castSucc))
    (ht : Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.succ)
        = q ^ dt * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.castSucc)) :
    ∃ l0 l1 : ℕ,
      Nat.card (fppfCohomology specInt L 0) = q ^ l0 ∧
      Nat.card (fppfCohomology specInt L 1) = q ^ l1 ∧
      (l1 : ℤ) - l0 + (if flag.kind i = JZeroFlagLayerKind.const then 1 else 0) ≤ (dg : ℤ) - dt := by sorry
