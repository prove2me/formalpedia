-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_pic0_complex_quotient_periodLattice
-- name    : ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_pic0_complex_quotient_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/553ef950-c5ec-5ded-8c34-a0885190d3eb
-- title:
--   Hecke-equivariant Abel–Jacobi injection for Pic⁰ of X₀(N)
-- statement:
--   Let $N$ be a nonzero natural number. Assume two hypotheses. First, for every prime $\ell$ the predicate [`ModularCurve.HeckeInputsAlong ℂ N ℓ`](def/ModularCurve_HeckeOperatorTotal.html#L13) holds, i.e. there are: integrality of the two level-raising maps $\bar\alpha,\bar\beta$ at level $N\ell$ over $\mathbb C$, the property that every nonzero element of the base-changed function field of level $N\ell$ has a divisor of degree $0$, finiteness of the extension along $\bar\alpha$, and moreover the fundamental identity along $\bar\beta$ together with the pushforward norm formula along $\bar\alpha$; these inputs are exactly what makes [`ModularCurve.heckeOperatorAlong ℂ N ℓ`](def/ModularCurve_HeckeOperatorTotal.html#L22) the correspondence-induced endomorphism of $\mathrm{Pic}^0$ rather than $0$. Second, [`ModularCurve.PeriodLatticeHeckeStable N`](def/ModularCurve_PeriodLattice.html#L223): for each prime $\ell$, the lattice $\Lambda_N =$ [`ModularCurve.periodLattice N`](def/ModularCurve_PeriodLattice.html#L102) (the $\mathbb Z$-span of the range of [`ModularCurve.period N`](def/ModularCurve_PeriodLattice.html#L92) inside the complex dual of $S_2(\Gamma_0(N)) =$ `CuspForm (CongruenceSubgroup.Gamma0 N) 2`) is carried into itself by [`ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ℓ)`](def/ModularCurve_PeriodLattice.html#L198), the transpose of the analytic Hecke action attached to the generator $X_\ell$ of the abstract Hecke algebra. Then there exists an additive group homomorphism $v$ from $\mathrm{Pic}^0$ of the field [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103) over $\mathbb C$ — degree-zero divisors, i.e. finitely supported $\mathbb Z$-valued functions on the places of that field, modulo principal ones — to $S_2(\Gamma_0(N))^\vee/\Lambda_N$ such that: $v$ is injective; every element of finite additive order of $S_2(\Gamma_0(N))^\vee/\Lambda_N$ lies in the range of $v$ (surjectivity itself is not asserted); and for every prime $\ell$, every class $z$ and every functional $\varphi$ with $v(z) = \varphi \bmod \Lambda_N$, one has $v(\mathrm{heckeOperatorAlong}\,\mathbb C\,N\,\ell\,(z)) = \mathrm{dualHeckeRep}\,N\,(X_\ell)(\varphi) \bmod \Lambda_N$.
--
--   This is the Abel–Jacobi theorem for the compact Riemann surface $X_0(N)(\mathbb C)$ in the present algebraic formulation, combined with the Eichler–Shimura compatibility between the algebraic Hecke correspondences on $\mathrm{Pic}^0$ and the transposed analytic Hecke action on $S_2(\Gamma_0(N))^\vee$, with the conclusion weakened from an isomorphism to an injection whose image contains all torsion. It is used to transport torsion of the complex Jacobian, with its Hecke action, to the divisor class group, and is cited by [`ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice`](thm.html#ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_pic0_complex_quotient_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_ModularCurve_PeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_pic0_complex_quotient_periodLattice
    (N : ℕ) [NeZero N]
    (hinC : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ N ℓ)
    (hst : ModularCurve.PeriodLatticeHeckeStable N) :
    ∃ v : AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) →+
        (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ ModularCurve.periodLattice N),
      Function.Injective v ∧
      (∀ y, IsOfFinAddOrder y → y ∈ v.range) ∧
      ∀ (ℓ : Nat.Primes)
        (z : AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)))
        (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.heckeOperatorAlong ℂ N ℓ) z) =
          Submodule.Quotient.mk (ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ℓ) φ) := by sorry
